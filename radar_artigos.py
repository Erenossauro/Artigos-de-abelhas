#!/usr/bin/env python3
"""
Radar de artigos científicos — versão SITE
------------------------------------------
Uso:
  python radar_artigos.py diario              # busca novidades e atualiza docs/index.html
  python radar_artigos.py diario --dias 30    # janela maior
  python radar_artigos.py diario --sem-email  # não envia e-mail (mesmo se ativado no config)
  python radar_artigos.py classicos           # exporta lista de clássicos em CSV

Fontes (gratuitas, sem chave obrigatória):
  - OpenAlex   (~250 milhões de trabalhos, com contagem de citações)
  - Europe PMC (PubMed + preprints como bioRxiv)

Variáveis de ambiente (todas opcionais):
  OPENALEX_MAILTO, OPENALEX_API_KEY  -> boas práticas da OpenAlex
  SMTP_USER, SMTP_PASS, EMAIL_TO     -> só se quiser também receber por e-mail
"""
import argparse
import csv
import html
import json
import os
import re
import smtplib
import ssl
import sys
import time
from datetime import date, timedelta
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
from pathlib import Path

import requests
import yaml

ROOT = Path(__file__).parent
STATE_FILE = ROOT / "state.json"
DOCS_DIR = ROOT / "docs"
CLASSICOS_DIR = ROOT / "classicos"

OPENALEX_URL = "https://api.openalex.org/works"
EPMC_URL = "https://www.ebi.ac.uk/europepmc/webservices/rest/search"


# ----------------------------------------------------------------------------
# Utilidades
# ----------------------------------------------------------------------------
def log(msg):
    print(msg, file=sys.stderr)


def load_config():
    with open(ROOT / "config.yaml", encoding="utf-8") as f:
        return yaml.safe_load(f)


def load_state():
    if STATE_FILE.exists():
        return json.loads(STATE_FILE.read_text(encoding="utf-8"))
    return {"vistos": [], "arquivo": [], "fila_classicos": {}}


def save_state(state):
    STATE_FILE.write_text(
        json.dumps(state, ensure_ascii=False, indent=1), encoding="utf-8"
    )


def get_json(url, params, tries=3):
    headers = {"User-Agent": "radar-artigos/2.0 (pesquisa academica)"}
    for i in range(tries):
        try:
            r = requests.get(url, params=params, headers=headers, timeout=45)
            if r.status_code == 429 or r.status_code >= 500:
                time.sleep(3 * (i + 1))
                continue
            r.raise_for_status()
            return r.json()
        except requests.RequestException:
            if i == tries - 1:
                raise
            time.sleep(3 * (i + 1))
    return {}


def norm_title(t):
    return re.sub(r"[^a-z0-9]+", " ", (t or "").lower()).strip()


def make_key(rec):
    if rec.get("doi"):
        return "doi:" + rec["doi"].lower()
    return "t:" + norm_title(rec.get("titulo"))


def clean_doi(doi):
    if not doi:
        return ""
    return re.sub(r"^https?://(dx\.)?doi\.org/", "", doi.strip(), flags=re.I)


def strip_tags(s):
    return re.sub(r"<[^>]+>", "", s or "")


# ----------------------------------------------------------------------------
# Filtro de revistas
# ----------------------------------------------------------------------------
def norm_j(s):
    return re.sub(r"[^a-z0-9]+", " ", (s or "").lower()).strip()


def match_j(nome, entrada):
    """Entrada normal: basta o nome da revista CONTER o texto.
    Entrada começando com '=': o nome precisa ser IGUAL (ex.: =Science)."""
    e = entrada.strip()
    if not e:
        return False
    if e.startswith("="):
        return nome == norm_j(e[1:])
    return norm_j(e) in nome


def revista_ok(revista, cfg):
    f = cfg.get("filtro_revistas") or {}
    if not f.get("ativo"):
        return True
    nome = norm_j(revista)
    for b in f.get("bloqueadas") or []:
        if match_j(nome, b):
            return False
    permitidas = f.get("permitidas") or []
    if not permitidas:
        return True
    return any(match_j(nome, p) for p in permitidas)


# ----------------------------------------------------------------------------
# Exclusão de assuntos (ex.: Apis mellifera)
# ----------------------------------------------------------------------------
def excluida(rec, cfg):
    ex = cfg.get("excluir") or {}
    termos = [t.lower() for t in (ex.get("termos") or []) if t]
    if not termos:
        return False
    titulo = (rec.get("titulo") or "").lower()
    resumo = (rec.get("resumo") or "").lower()
    manter = [m.lower() for m in (ex.get("manter_se_no_titulo") or []) if m]
    if any(m in titulo for m in manter):
        return False
    texto = titulo if ex.get("onde", "titulo") == "titulo" else titulo + " " + resumo
    return any(t in texto for t in termos)


# ----------------------------------------------------------------------------
# Construção das consultas
# ----------------------------------------------------------------------------
def build_or(terms, field=None):
    parts = []
    for t in terms:
        t = t.strip()
        q = f'"{t}"' if (" " in t or "-" in t) else t
        parts.append(f"{field}:{q}" if field else q)
    return "(" + " OR ".join(parts) + ")"


def topic_query(topico, field=None):
    q = build_or(topico["termos"], field)
    if topico.get("contexto"):
        q += " AND " + build_or(topico["contexto"], field)
    return q


# ----------------------------------------------------------------------------
# Fontes
# ----------------------------------------------------------------------------
def abstract_from_inverted(inv):
    if not inv:
        return ""
    pos = {}
    for word, idxs in inv.items():
        for i in idxs:
            pos[i] = word
    return " ".join(pos[i] for i in sorted(pos))


def openalex_search(topico, ini=None, fim=None, sort="publication_date:desc",
                    per_page=100, ate_ano=None, paginas=1):
    filtros = [f"title_and_abstract.search:{topic_query(topico)}",
               "type:article|preprint"]
    if ini:
        filtros.append(f"from_publication_date:{ini}")
    if fim:
        filtros.append(f"to_publication_date:{fim}")
    if ate_ano:
        filtros.append(f"to_publication_date:{ate_ano}-12-31")
    params = {"filter": ",".join(filtros), "sort": sort, "per-page": per_page}
    if os.getenv("OPENALEX_MAILTO"):
        params["mailto"] = os.environ["OPENALEX_MAILTO"]
    if os.getenv("OPENALEX_API_KEY"):
        params["api_key"] = os.environ["OPENALEX_API_KEY"]

    resultados = []
    for pag in range(1, paginas + 1):
        params["page"] = pag
        data = get_json(OPENALEX_URL, params)
        lote = data.get("results", [])
        resultados += lote
        if len(lote) < per_page:
            break
    out = []
    for w in resultados:
        loc = w.get("primary_location") or {}
        src = loc.get("source") or {}
        autores = [
            (a.get("author") or {}).get("display_name", "")
            for a in (w.get("authorships") or [])
        ]
        doi = clean_doi(w.get("doi"))
        rec = {
            "titulo": strip_tags(w.get("display_name") or w.get("title") or ""),
            "autores": autores,
            "revista": src.get("display_name") or "",
            "data": w.get("publication_date") or "",
            "ano": w.get("publication_year"),
            "resumo": abstract_from_inverted(w.get("abstract_inverted_index")),
            "doi": doi,
            "url": f"https://doi.org/{doi}" if doi else (w.get("id") or ""),
            "citacoes": w.get("cited_by_count", 0),
            "fonte": "OpenAlex",
        }
        rec["key"] = make_key(rec)
        out.append(rec)
    return out


def epmc_search(topico, ini, fim, page_size=100):
    q = topic_query(topico, field="TITLE_ABS")
    q = f"({q}) AND (FIRST_PDATE:[{ini} TO {fim}])"
    params = {"query": q, "format": "json", "resultType": "core",
              "pageSize": page_size, "sort": "P_PDATE_D desc"}
    data = get_json(EPMC_URL, params)
    out = []
    for w in (data.get("resultList") or {}).get("result", []):
        doi = clean_doi(w.get("doi"))
        autores = [a.strip() for a in (w.get("authorString") or "").rstrip(".").split(",") if a.strip()]
        rec = {
            "titulo": strip_tags(w.get("title") or "").rstrip("."),
            "autores": autores,
            "revista": w.get("journalTitle") or w.get("source", ""),
            "data": w.get("firstPublicationDate") or "",
            "ano": int(w["pubYear"]) if str(w.get("pubYear", "")).isdigit() else None,
            "resumo": strip_tags(w.get("abstractText") or ""),
            "doi": doi,
            "url": f"https://doi.org/{doi}" if doi else
                   f"https://europepmc.org/article/{w.get('source')}/{w.get('id')}",
            "citacoes": w.get("citedByCount", 0),
            "fonte": "Europe PMC",
        }
        rec["key"] = make_key(rec)
        out.append(rec)
    return out


# ----------------------------------------------------------------------------
# Pontuação e deduplicação
# ----------------------------------------------------------------------------
def score(rec, topico):
    termos = [t.lower() for t in topico["termos"] + topico.get("contexto", [])]
    titulo = rec["titulo"].lower()
    resumo = rec["resumo"].lower()
    s = 0
    for t in termos:
        padrao = r"\b" + re.escape(t) + r"(s|es)?\b"
        if re.search(padrao, titulo):
            s += 3
        if re.search(padrao, resumo):
            s += 1
    return s


def dedup(recs):
    vistos, out = {}, []
    for r in recs:
        k = r["key"]
        tk = "t:" + norm_title(r["titulo"])
        if k in vistos or tk in vistos:
            ex = vistos.get(k) or vistos.get(tk)
            if not ex["resumo"] and r["resumo"]:
                ex["resumo"] = r["resumo"]
            continue
        vistos[k] = r
        vistos[tk] = r
        out.append(r)
    return out


# ----------------------------------------------------------------------------
# Registros para o site
# ----------------------------------------------------------------------------
def para_site(r, topico, tipo, adicionado):
    autores = ", ".join(r["autores"][:6]) + (" et al." if len(r["autores"]) > 6 else "")
    resumo = r.get("resumo") or ""
    if len(resumo) > 600:
        resumo = resumo[:600].rsplit(" ", 1)[0] + "…"
    return {
        "key": r["key"],
        "titulo": r["titulo"],
        "autores": autores,
        "revista": r.get("revista", ""),
        "data": r.get("data", ""),
        "ano": r.get("ano"),
        "resumo": resumo,
        "url": r["url"],
        "citacoes": r.get("citacoes", 0),
        "fonte": r.get("fonte", ""),
        "topico": topico,
        "tipo": tipo,
        "adicionado": adicionado,
    }


SITE_TEMPLATE = r"""<!doctype html>
<html lang="pt-BR">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>__TITULO__</title>
<style>
  :root { --bg:#fbfaf6; --card:#ffffff; --txt:#222; --mut:#6b6b6b; --line:#e6e2d6; --acc:#b7791f; --acc2:#7a4e0a; }
  @media (prefers-color-scheme: dark) {
    :root { --bg:#17150f; --card:#201d14; --txt:#ece8dc; --mut:#a39d8a; --line:#34301f; --acc:#e0a63c; --acc2:#f0c36d; }
  }
  * { box-sizing:border-box; }
  body { margin:0; background:var(--bg); color:var(--txt); font-family:Georgia,'Times New Roman',serif; line-height:1.5; }
  header { padding:28px 16px 8px; max-width:820px; margin:auto; }
  h1 { margin:0; font-size:26px; }
  .sub { color:var(--mut); font-size:14px; margin-top:4px; font-family:Arial,sans-serif; }
  main { max-width:820px; margin:auto; padding:8px 16px 60px; font-family:Arial,Helvetica,sans-serif; }
  .tabs { display:flex; gap:8px; margin:16px 0 10px; }
  .tab { padding:8px 16px; border:1px solid var(--line); background:var(--card); color:var(--txt); border-radius:20px; cursor:pointer; font-size:14px; }
  .tab.on { background:var(--acc); border-color:var(--acc); color:#fff; }
  .chips { display:flex; flex-wrap:wrap; gap:6px; margin:6px 0 12px; }
  .chip { padding:4px 11px; font-size:12px; border:1px solid var(--line); border-radius:14px; cursor:pointer; background:var(--card); color:var(--mut); }
  .chip.on { border-color:var(--acc); color:var(--acc2); font-weight:bold; }
  select { width:100%; padding:9px 10px; font-size:14px; border:1px solid var(--line); border-radius:8px; background:var(--card); color:var(--txt); margin-bottom:8px; }
  input[type=search] { width:100%; padding:10px 12px; font-size:15px; border:1px solid var(--line); border-radius:8px; background:var(--card); color:var(--txt); }
  .count { color:var(--mut); font-size:12px; margin:10px 0; }
  h2.dia { font-size:14px; color:var(--acc2); border-bottom:2px solid var(--acc); padding-bottom:3px; margin:26px 0 12px; font-family:Arial,sans-serif; }
  .item { background:var(--card); border:1px solid var(--line); border-radius:10px; padding:14px 16px; margin-bottom:12px; }
  .item a.t { font-size:16px; font-weight:bold; color:var(--acc2); text-decoration:none; font-family:Georgia,serif; }
  .item a.t:hover { text-decoration:underline; }
  .aut { font-size:13px; color:var(--mut); margin-top:3px; }
  .meta { font-size:12px; color:var(--mut); margin:4px 0 8px; }
  .tag { display:inline-block; font-size:11px; background:var(--line); padding:1px 8px; border-radius:10px; margin-right:6px; color:var(--txt); }
  .res { font-size:13.5px; }
  button.mais { display:block; margin:18px auto; padding:10px 22px; border-radius:20px; border:1px solid var(--acc); background:transparent; color:var(--acc2); cursor:pointer; font-size:14px; }
  footer { text-align:center; color:var(--mut); font-size:11px; padding:20px; font-family:Arial,sans-serif; }
</style>
</head>
<body>
<header>
  <h1>🐝 __TITULO__</h1>
  <div class="sub">__SUBTITULO__ · atualizado em __ATUALIZADO__</div>
</header>
<main>
  <div class="tabs">
    <button class="tab on" id="tab-novo" onclick="setAba('novo')">Novidades</button>
    <button class="tab" id="tab-classico" onclick="setAba('classico')">Clássicos</button>
  </div>
  <div class="chips" id="chips"></div>
  <select id="rev" onchange="setRev(this.value)"></select>
  <input type="search" id="busca" placeholder="Buscar por palavra no título, autor ou resumo…" oninput="setBusca(this.value)">
  <div class="count" id="count"></div>
  <div id="lista"></div>
  <button class="mais" id="mais" onclick="mostrarMais()" style="display:none">Mostrar mais</button>
</main>
<footer>Montado automaticamente com dados abertos do OpenAlex e do Europe PMC.</footer>
<script>
const DADOS = __DADOS__;
const POR_PAGINA = 40;
let aba = 'novo', topico = '', busca = '', revista = '', limite = POR_PAGINA;

function esc(s) {
  return String(s == null ? '' : s).replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
}
function fmtData(s) {
  if (!s) return '';
  const d = new Date(s + 'T00:00:00');
  return isNaN(d) ? s : d.toLocaleDateString('pt-BR');
}
function setAba(a) { aba = a; limite = POR_PAGINA;
  document.getElementById('tab-novo').classList.toggle('on', a === 'novo');
  document.getElementById('tab-classico').classList.toggle('on', a === 'classico');
  render(); }
function setTopico(t) { topico = t; limite = POR_PAGINA; render(); }
function setRev(v) { revista = v; limite = POR_PAGINA; render(); }
function setBusca(v) { busca = v.toLowerCase().trim(); limite = POR_PAGINA; render(); }
function mostrarMais() { limite += POR_PAGINA; render(); }

function filtrados() {
  let xs = DADOS.filter(d => d.tipo === aba);
  if (topico) xs = xs.filter(d => d.topico === topico);
  if (revista) xs = xs.filter(d => d.revista === revista);
  if (busca) xs = xs.filter(d =>
    (d.titulo + ' ' + d.autores + ' ' + d.resumo + ' ' + d.revista).toLowerCase().includes(busca));
  if (aba === 'novo') {
    xs.sort((a, b) => (b.adicionado || '').localeCompare(a.adicionado || '') || (b.data || '').localeCompare(a.data || ''));
  } else {
    xs.sort((a, b) => (b.citacoes || 0) - (a.citacoes || 0));
  }
  return xs;
}

function itemHtml(d) {
  const meta = [esc(d.revista), fmtData(d.data) || esc(d.ano || ''),
    aba === 'classico' ? (d.citacoes || 0) + ' citações' : ''].filter(Boolean).join(' · ');
  return '<div class="item">' +
    '<a class="t" href="' + esc(d.url) + '" target="_blank" rel="noopener">' + esc(d.titulo) + '</a>' +
    '<div class="aut">' + esc(d.autores) + '</div>' +
    '<div class="meta"><span class="tag">' + esc(d.topico) + '</span>' + meta + '</div>' +
    '<div class="res">' + (d.resumo ? esc(d.resumo) : '<i>(sem resumo disponível)</i>') + '</div></div>';
}

function render() {
  const topicos = [...new Set(DADOS.filter(d => d.tipo === aba).map(d => d.topico))];
  document.getElementById('chips').innerHTML =
    '<span class="chip ' + (topico === '' ? 'on' : '') + '" onclick="setTopico(\'\')">Todos</span>' +
    topicos.map(t => '<span class="chip ' + (topico === t ? 'on' : '') + '" data-t="' + esc(t) + '">' + esc(t) + '</span>').join('');
  document.querySelectorAll('.chip[data-t]').forEach(el => el.onclick = () => setTopico(el.dataset.t));

  const contagem = {};
  DADOS.filter(d => d.tipo === aba && (!topico || d.topico === topico) && d.revista)
       .forEach(d => { contagem[d.revista] = (contagem[d.revista] || 0) + 1; });
  const revistas = Object.keys(contagem).sort((a, b) => contagem[b] - contagem[a]);
  if (revista && !revistas.includes(revista)) revista = '';
  const sel = document.getElementById('rev');
  sel.innerHTML = '<option value="">Todas as revistas (' + revistas.length + ')</option>' +
    revistas.map(r => '<option value="' + esc(r) + '">' + esc(r) + ' (' + contagem[r] + ')</option>').join('');
  sel.value = revista;

  const xs = filtrados();
  document.getElementById('count').textContent = xs.length + ' artigo(s)';
  const parte = xs.slice(0, limite);
  let out = '', diaAtual = null;
  for (const d of parte) {
    if (aba === 'novo' && d.adicionado !== diaAtual) {
      diaAtual = d.adicionado;
      out += '<h2 class="dia">Chegaram em ' + fmtData(diaAtual) + '</h2>';
    }
    out += itemHtml(d);
  }
  if (!parte.length) out = '<p style="color:var(--mut)">Nada encontrado.</p>';
  document.getElementById('lista').innerHTML = out;
  document.getElementById('mais').style.display = xs.length > limite ? 'block' : 'none';
}
render();
</script>
</body>
</html>
"""


def gerar_site(cfg, state, hoje):
    itens = [d for d in state.get("arquivo", [])
             if revista_ok(d.get("revista"), cfg) and not excluida(d, cfg)]
    for nome, fila in state.get("fila_classicos", {}).items():
        for r in fila:
            if revista_ok(r.get("revista"), cfg) and not excluida(r, cfg):
                itens.append(para_site(r, nome, "classico", ""))
    dados = json.dumps(itens, ensure_ascii=False).replace("</", "<\\/")
    site = cfg.get("site", {})
    pagina = (SITE_TEMPLATE
              .replace("__TITULO__", html.escape(site.get("titulo", "Radar de artigos")))
              .replace("__SUBTITULO__", html.escape(site.get("subtitulo", "")))
              .replace("__ATUALIZADO__", hoje.strftime("%d/%m/%Y"))
              .replace("__DADOS__", dados))
    DOCS_DIR.mkdir(exist_ok=True)
    (DOCS_DIR / "index.html").write_text(pagina, encoding="utf-8")
    (DOCS_DIR / ".nojekyll").write_text("", encoding="utf-8")
    log(f"Site gerado em docs/index.html ({len(itens)} artigos)")


# ----------------------------------------------------------------------------
# E-mail (opcional)
# ----------------------------------------------------------------------------
def montar_email(titulo, novos):
    corpo = [f"<h2>{html.escape(titulo)}</h2>"]
    texto = []
    for r in novos:
        corpo.append(
            f"<p><a href='{html.escape(r['url'])}'><b>{html.escape(r['titulo'])}</b></a><br>"
            f"<small>{html.escape(r['topico'])} · {html.escape(r['autores'])}</small><br>"
            f"{html.escape(r['resumo'])}</p>")
        texto.append(f"[{r['topico']}] {r['titulo']}\n  {r['url']}")
    return "".join(corpo), "\n\n".join(texto) or "Nenhum artigo novo hoje."


def enviar_email(cfg, assunto, html_body, text_body):
    user = os.getenv("SMTP_USER")
    senha = os.getenv("SMTP_PASS")
    destino = os.getenv("EMAIL_TO") or cfg["email"].get("destinatario") or user
    if not (user and senha and destino):
        log("⚠ SMTP_USER/SMTP_PASS/EMAIL_TO não definidos — e-mail não enviado.")
        return False
    msg = MIMEMultipart("alternative")
    msg["Subject"], msg["From"], msg["To"] = assunto, user, destino
    msg.attach(MIMEText(text_body, "plain", "utf-8"))
    msg.attach(MIMEText(html_body, "html", "utf-8"))
    with smtplib.SMTP_SSL(cfg["email"]["servidor_smtp"], cfg["email"]["porta_smtp"],
                          context=ssl.create_default_context()) as s:
        s.login(user, senha)
        s.sendmail(user, [destino], msg.as_string())
    log(f"✔ E-mail enviado para {destino}")
    return True


# ----------------------------------------------------------------------------
# Modo diário
# ----------------------------------------------------------------------------
def leve(r):
    d = dict(r)
    d["resumo"] = (d.get("resumo") or "")[:600]
    return d


def garantir_fila_classicos(cfg, state):
    c = cfg["classicos"]
    h = json.dumps([cfg.get("filtro_revistas"), cfg.get("excluir"), c, cfg["topicos"]],
                   sort_keys=True, default=str)
    if state.get("classicos_hash") != h:
        state["fila_classicos"] = {}      # filtro mudou: refaz a lista
        state["classicos_hash"] = h
    fila = state.setdefault("fila_classicos", {})
    filtro_on = bool((cfg.get("filtro_revistas") or {}).get("ativo")) or bool(
        (cfg.get("excluir") or {}).get("termos"))
    por_pagina = 200 if filtro_on else c["por_topico"]
    for t in cfg["topicos"]:
        if t["nome"] in fila:
            continue
        try:
            recs = openalex_search(t, sort="cited_by_count:desc",
                                   per_page=por_pagina, ate_ano=c.get("ate_ano"))
            recs = [r for r in recs
                    if revista_ok(r["revista"], cfg) and not excluida(r, cfg)][: c["por_topico"]]
            fila[t["nome"]] = [leve(r) for r in recs]
            log(f"Clássicos carregados: {t['nome']} ({len(recs)})")
        except Exception as e:
            log(f"Erro ao buscar clássicos de {t['nome']}: {e}")


def run_diario(cfg, state, dias, enviar):
    hoje = date.today()
    b = cfg["busca"]
    nomes = sorted(t["nome"] for t in cfg["topicos"])
    if state.get("nomes_topicos") != nomes:
        log("Lista de tópicos mudou: reiniciando o arquivo do site.")
        state["arquivo"], state["vistos"] = [], []
        state["nomes_topicos"] = nomes
    primeira = not state.get("arquivo")
    if dias is None:
        dias = b["primeira_vez_dias"] if primeira else b["dias_para_tras"]
    limite_topico = b["max_por_topico"] * (4 if primeira else 1)
    paginas = b.get("paginas", 3) * (3 if primeira else 1)
    ini = (hoje - timedelta(days=dias)).isoformat()
    fim = hoje.isoformat()

    vistos = set(state.setdefault("vistos", []))
    arquivo = state.setdefault("arquivo", [])
    todos_novos = []

    for t in cfg["topicos"]:
        recs = []
        if "openalex" in b["fontes"]:
            try:
                recs += openalex_search(t, ini, fim, paginas=paginas)
            except Exception as e:
                log(f"Erro OpenAlex ({t['nome']}): {e}")
        if "europepmc" in b["fontes"]:
            try:
                recs += epmc_search(t, ini, fim)
            except Exception as e:
                log(f"Erro Europe PMC ({t['nome']}): {e}")

        recs = dedup(recs)
        recs = [r for r in recs
                if revista_ok(r["revista"], cfg) and not excluida(r, cfg)]
        for r in recs:
            r["score"] = score(r, t)
        novos = [r for r in recs
                 if r["key"] not in vistos
                 and "t:" + norm_title(r["titulo"]) not in vistos
                 and r["score"] >= b["pontuacao_minima"]]
        novos.sort(key=lambda r: r["data"] or "", reverse=True)
        novos.sort(key=lambda r: r["score"], reverse=True)
        novos = novos[:limite_topico]
        for r in novos:
            vistos.add(r["key"])
            vistos.add("t:" + norm_title(r["titulo"]))
            reg = para_site(r, t["nome"], "novo", hoje.isoformat())
            arquivo.append(reg)
            todos_novos.append(reg)
        log(f"{t['nome']}: {len(novos)} novos")

    garantir_fila_classicos(cfg, state)

    state["vistos"] = sorted(vistos)
    state["arquivo"] = arquivo[-6000:]

    if enviar and cfg.get("email", {}).get("ativo"):
        titulo = f"Radar de artigos — {hoje.strftime('%d/%m/%Y')}"
        h, t_ = montar_email(titulo, todos_novos)
        if not enviar_email(cfg, f"📚 {titulo} ({len(todos_novos)} novos)", h, t_):
            log("E-mail falhou; o site foi atualizado mesmo assim.")

    gerar_site(cfg, state, hoje)
    save_state(state)


# ----------------------------------------------------------------------------
# Modo clássicos (exporta CSV)
# ----------------------------------------------------------------------------
def run_classicos(cfg):
    c = cfg["classicos"]
    CLASSICOS_DIR.mkdir(exist_ok=True)
    linhas = []
    for t in cfg["topicos"]:
        try:
            recs = openalex_search(t, sort="cited_by_count:desc",
                                   per_page=c["por_topico"], ate_ano=c.get("ate_ano"))
        except Exception as e:
            log(f"Erro em {t['nome']}: {e}")
            continue
        for r in recs:
            linhas.append([t["nome"], r["titulo"], "; ".join(r["autores"][:8]),
                           r["ano"], r["revista"], r["citacoes"], r["doi"], r["url"]])
    caminho = CLASSICOS_DIR / f"classicos_{date.today().isoformat()}.csv"
    with open(caminho, "w", newline="", encoding="utf-8-sig") as f:
        w = csv.writer(f)
        w.writerow(["tema", "titulo", "autores", "ano", "revista", "citacoes", "doi", "url"])
        w.writerows(linhas)
    log(f"Gerado: {caminho}")


# ----------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser(description="Radar de artigos científicos")
    ap.add_argument("modo", choices=["diario", "classicos"])
    ap.add_argument("--dias", type=int, help="janela de busca em dias")
    ap.add_argument("--sem-email", action="store_true", help="não envia e-mail")
    args = ap.parse_args()

    cfg = load_config()
    if args.modo == "classicos":
        run_classicos(cfg)
    else:
        run_diario(cfg, load_state(), args.dias, enviar=not args.sem_email)


if __name__ == "__main__":
    main()
