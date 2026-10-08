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
import io
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
# Categorias de filtro (grupo de abelhas, tipo de estudo, região...)
# ----------------------------------------------------------------------------
def _padrao(t):
    return re.compile(r"\b" + re.escape(t.strip().lower()) + r"(s|es)?\b")


def compilar_facetas(cfg):
    comp = []
    for f in cfg.get("filtros") or []:
        opcoes = []
        for o in f.get("opcoes") or []:
            opcoes.append((
                o["nome"],
                [_padrao(t) for t in (o.get("termos") or []) if str(t).strip()],
                [_padrao(t) for t in (o.get("termos_titulo") or []) if str(t).strip()],
            ))
        comp.append((f["nome"], f.get("rotulo_sem", "Não identificado"), opcoes))
    return comp


def classificar(titulo, resumo, comp):
    t = (titulo or "").lower()
    texto = t + " " + (resumo or "").lower()
    out = {}
    for nome, sem, opcoes in comp:
        marcadas = [on for on, p_todos, p_tit in opcoes
                    if any(p.search(texto) for p in p_todos) or any(p.search(t) for p in p_tit)]
        out[nome] = marcadas or [sem]
    return out


def definicao_filtros(cfg):
    """Lista de categorias e opções, na ordem do config, para o site."""
    return [{"nome": f["nome"],
             "opcoes": [o["nome"] for o in f.get("opcoes") or []] + [f.get("rotulo_sem", "Não identificado")]}
            for f in cfg.get("filtros") or []]


def hash_filtros(cfg):
    return json.dumps(cfg.get("filtros"), sort_keys=True, default=str, ensure_ascii=False)


# ----------------------------------------------------------------------------
# SJR (SCImago Journal Rank) — lido do arquivo sjr.csv, se existir
# ----------------------------------------------------------------------------
def _issn_norm(x):
    return re.sub(r"[^0-9Xx]", "", x or "").upper()


def carregar_sjr(cfg):
    """Devolve (por_issn, por_titulo): cada um mapeia para (sjr, quartil)."""
    nome = (cfg.get("sjr") or {}).get("arquivo", "sjr.csv")
    caminho = ROOT / nome
    if not caminho.exists():
        return {}, {}
    try:
        texto = caminho.read_text(encoding="utf-8-sig", errors="replace")
        primeira = texto.split("\n", 1)[0]
        delim = ";" if primeira.count(";") >= primeira.count(",") else ","
        leitor = csv.reader(io.StringIO(texto), delimiter=delim)
        cab = [h.strip().lower() for h in next(leitor, [])]

        def achar(pred):
            for i, h in enumerate(cab):
                if pred(h):
                    return i
            return None

        i_tit = achar(lambda h: h == "title")
        i_issn = achar(lambda h: h == "issn")
        i_sjr = achar(lambda h: h == "sjr")
        i_q = achar(lambda h: "quartile" in h)
        if i_sjr is None or (i_issn is None and i_tit is None):
            log("⚠ sjr.csv não tem as colunas esperadas (Title, Issn, SJR). Ignorando.")
            return {}, {}
        por_issn, por_titulo = {}, {}
        for linha in leitor:
            try:
                valor = float(linha[i_sjr].strip().replace(",", "."))
            except (ValueError, IndexError):
                continue
            q = linha[i_q].strip().upper() if i_q is not None and i_q < len(linha) else ""
            q = q if re.fullmatch(r"Q[1-4]", q) else ""
            if i_issn is not None and i_issn < len(linha):
                for tok in re.split(r"[,;\s]+", linha[i_issn]):
                    k = _issn_norm(tok)
                    if len(k) == 8:
                        por_issn[k] = (valor, q)
            if i_tit is not None and i_tit < len(linha):
                por_titulo[norm_j(linha[i_tit])] = (valor, q)
        log(f"SJR carregado: {len(por_issn)} ISSNs, {len(por_titulo)} títulos")
        return por_issn, por_titulo
    except Exception as e:
        log(f"⚠ Não consegui ler o sjr.csv: {e}")
        return {}, {}


def sjr_de(d, por_issn, por_titulo):
    for i in d.get("issn") or []:
        hit = por_issn.get(_issn_norm(i))
        if hit:
            return hit
    return por_titulo.get(norm_j(d.get("revista")))


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
            "issn": [i for i in ((src.get("issn") or []) + [src.get("issn_l")]) if i],
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
            "issn": [i for i in [((w.get("journalInfo") or {}).get("journal") or {}).get("issn"),
                                 ((w.get("journalInfo") or {}).get("journal") or {}).get("essn")] if i],
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
        "facetas": r.get("facetas") or {},
        "issn": r.get("issn") or [],
    }


SITE_TEMPLATE = r"""<!doctype html>
<html lang="pt-BR">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>__TITULO__</title>
<link rel="icon" href="data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 64 64'%3E%3Cpolygon points='32,3 58,18 58,46 32,61 6,46 6,18' fill='%23FFC933'/%3E%3C/svg%3E">
<style>
  :root {
    --bg:#FFFDF5; --surface:#FFFFFF; --surface2:#FFF7DB; --ink:#2A2208; --mut:#7C6F48; --line:#F1E7C6;
    --amarelo:#FFC933; --amarelo2:#F5B800; --suave:#FFEFB8; --acento:#8A5E00;
    --ok:#2F7D4F; --err:#B3261E;
    --sombra:0 1px 2px rgba(120,90,0,.06), 0 8px 24px rgba(120,90,0,.08);
    --raio:18px;
  }
  @media (prefers-color-scheme: dark) {
    :root {
      --bg:#15120A; --surface:#1F1B0E; --surface2:#2A2410; --ink:#F7EFD8; --mut:#B3A777; --line:#37301A;
      --amarelo:#FFCB3D; --amarelo2:#FFD966; --suave:#4A3C0F; --acento:#FFD966;
      --ok:#6FCF97; --err:#FF8A80;
      --sombra:0 1px 2px rgba(0,0,0,.3), 0 8px 24px rgba(0,0,0,.25);
    }
  }
  * { box-sizing:border-box; }
  html { scroll-behavior:smooth; }
  body { margin:0; background:var(--bg); color:var(--ink); line-height:1.5;
    font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,"Helvetica Neue",Arial,sans-serif; }
  a { color:inherit; }

  /* ---------- topo ---------- */
  .topo { background:linear-gradient(180deg,var(--surface2),var(--bg)); border-bottom:1px solid var(--line); }
  .topo-in { max-width:1180px; margin:auto; padding:22px 20px 18px; display:flex; align-items:center; gap:14px; }
  .marca { display:flex; align-items:center; gap:14px; }
  .marca svg { flex:none; filter:drop-shadow(0 4px 8px rgba(184,134,0,.25)); }
  .marca h1 { margin:0; font-size:26px; letter-spacing:-.02em; font-weight:800; }
  .marca .sub { color:var(--mut); font-size:13.5px; margin-top:1px; }
  .conta { max-width:1180px; margin:12px auto 0; padding:0 20px; font-size:14px; display:flex; flex-wrap:wrap; gap:8px; align-items:center; }
  .conta input[type=email] { flex:1; min-width:210px; max-width:340px; padding:9px 14px; font-size:14px; border:1px solid var(--line); border-radius:999px; background:var(--surface); color:var(--ink); }
  .conta .msg { width:100%; font-size:12px; color:var(--mut); }

  /* ---------- layout ---------- */
  .layout { max-width:1180px; margin:18px auto 60px; padding:0 20px; display:grid; grid-template-columns:290px minmax(0,1fr); gap:28px; align-items:start; }
  .layout.sem-sidebar { grid-template-columns:minmax(0,1fr); }
  .layout.sem-sidebar .sidebar { display:none; }
  .sidebar { position:sticky; top:14px; max-height:calc(100vh - 28px); overflow:auto; padding-right:4px; }
  .sb-bloco { background:var(--surface); border:1px solid var(--line); border-radius:var(--raio); padding:14px 14px 10px; margin-bottom:14px; box-shadow:var(--sombra); }
  .sb-titulo { font-size:13px; font-weight:800; letter-spacing:.04em; text-transform:uppercase; color:var(--acento); margin-bottom:8px; }
  .sb-bloco select { width:100%; padding:9px 12px; font-size:14px; border:1px solid var(--line); border-radius:12px; background:var(--bg); color:var(--ink); margin-bottom:8px; }
  .sb-bloco input[type=search] { width:100%; padding:8px 12px; font-size:13px; border:1px solid var(--line); border-radius:999px; background:var(--bg); color:var(--ink); margin-bottom:6px; }
  .linha-btns { display:flex; gap:6px; flex-wrap:wrap; }
  .perfil-info { font-size:12px; color:var(--mut); margin-top:8px; }
  .lista-op { max-height:260px; overflow:auto; margin:0 -4px; padding:0 4px; }
  label.op { display:flex; align-items:center; gap:9px; padding:6px 6px; border-radius:10px; cursor:pointer; font-size:14px; position:relative; }
  label.op:hover { background:var(--surface2); }
  label.op input { position:absolute; opacity:0; pointer-events:none; }
  label.op .ck { flex:none; width:18px; height:18px; border:2px solid var(--amarelo2); border-radius:6px; background:var(--surface); display:inline-block; position:relative; }
  label.op input:checked + .ck { background:var(--amarelo); border-color:var(--amarelo2); }
  label.op input:checked + .ck::after { content:""; position:absolute; left:4px; top:0; width:5px; height:10px; border:solid var(--ink); border-width:0 2px 2px 0; transform:rotate(45deg); }
  label.op input:focus-visible + .ck { outline:2px solid var(--acento); outline-offset:2px; }
  label.op .nome { flex:1; min-width:0; line-height:1.25; }
  label.op .n { font-size:12px; color:var(--mut); background:var(--surface2); border-radius:999px; padding:1px 8px; }
  label.op.zero { opacity:.45; }
  .mais-filtros { width:100%; margin-bottom:14px; }
  .fnota { font-size:11px; color:var(--mut); margin:2px 4px 14px; }

  /* ---------- botões ---------- */
  .btn { padding:8px 16px; border:1.5px solid var(--amarelo2); background:transparent; color:var(--acento); border-radius:999px; cursor:pointer; font-size:13px; font-weight:600; font-family:inherit; }
  .btn:hover { background:var(--suave); }
  .btn.forte { background:var(--amarelo); border-color:var(--amarelo); color:#2A2208; }
  .btn.forte:hover { background:var(--amarelo2); }
  .btn.perigo { border-color:var(--err); color:var(--err); }
  .btn.mini { padding:4px 12px; font-size:12px; }
  .btn.largo { width:100%; }

  /* ---------- barra de abas ---------- */
  .barra { display:flex; flex-wrap:wrap; gap:10px; align-items:center; justify-content:space-between; margin-bottom:14px; }
  .seg { display:inline-flex; background:var(--surface2); border:1px solid var(--line); border-radius:999px; padding:4px; gap:2px; flex-wrap:wrap; }
  .seg button { border:none; background:transparent; color:var(--mut); padding:9px 20px; border-radius:999px; font-size:14px; font-weight:700; cursor:pointer; font-family:inherit; }
  .seg button.on { background:var(--amarelo); color:#2A2208; box-shadow:0 2px 8px rgba(184,134,0,.25); }
  .btn-filtros { display:none; }
  .busca-linha { display:flex; flex-wrap:wrap; gap:10px; margin-bottom:6px; }
  .busca-linha input[type=search] { flex:1; min-width:220px; padding:12px 18px; font-size:15px; border:1px solid var(--line); border-radius:999px; background:var(--surface); color:var(--ink); box-shadow:var(--sombra); }
  .busca-linha select { padding:11px 16px; font-size:14px; border:1px solid var(--line); border-radius:999px; background:var(--surface); color:var(--ink); }
  .count { color:var(--mut); font-size:13px; margin:12px 4px; }

  /* ---------- cartões de artigo ---------- */
  h2.dia { font-size:13px; font-weight:800; letter-spacing:.05em; text-transform:uppercase; color:var(--acento); margin:26px 4px 12px; display:flex; align-items:center; gap:10px; }
  h2.dia::after { content:""; flex:1; height:2px; background:var(--suave); border-radius:2px; }
  .card { background:var(--surface); border:1px solid var(--line); border-radius:var(--raio); padding:16px 20px 14px; margin-bottom:14px; box-shadow:var(--sombra); transition:transform .12s, border-color .12s; }
  .card:hover { transform:translateY(-1px); border-color:var(--amarelo2); }
  .card-top { display:flex; justify-content:space-between; gap:12px; align-items:flex-start; font-size:13px; }
  .rv { display:flex; flex-wrap:wrap; gap:8px; align-items:center; min-width:0; }
  .rev { font-weight:700; color:var(--acento); }
  .rev.mut { color:var(--mut); font-weight:500; }
  .sjr { background:var(--suave); color:var(--ink); border-radius:999px; padding:2px 10px; font-size:12px; font-weight:700; white-space:nowrap; }
  .data { color:var(--mut); font-weight:600; white-space:nowrap; font-size:13px; }
  .titulo { display:block; margin:8px 0 4px; font-size:20px; line-height:1.3; font-weight:800; letter-spacing:-.01em; text-decoration:none; color:var(--ink); }
  .titulo:hover { color:var(--acento); text-decoration:underline; text-decoration-color:var(--amarelo); text-underline-offset:3px; }
  .autores { font-size:14px; color:var(--mut); }
  details.det { margin-top:10px; }
  details.det summary { cursor:pointer; font-size:13px; font-weight:700; color:var(--acento); list-style:none; }
  details.det summary::-webkit-details-marker { display:none; }
  details.det summary::before { content:"▸ "; }
  details.det[open] summary::before { content:"▾ "; }
  .det-in { margin-top:8px; }
  .res { font-size:14px; color:var(--ink); opacity:.88; }
  .tags { margin-bottom:8px; }
  .tag { display:inline-block; font-size:11.5px; background:var(--surface2); border:1px solid var(--line); padding:2px 10px; border-radius:999px; margin:0 6px 4px 0; color:var(--mut); font-weight:600; }
  .meta { font-size:12px; color:var(--mut); margin:6px 0; }
  .nota { font-size:14px; background:var(--surface2); border-left:4px solid var(--amarelo); padding:8px 12px; margin:10px 0; border-radius:8px; }
  .botoes { display:flex; flex-wrap:wrap; gap:8px; margin-top:12px; }

  /* ---------- painéis, laboratório ---------- */
  .painel { background:var(--surface); border:2px solid var(--amarelo); border-radius:var(--raio); padding:18px; margin:0 0 16px; box-shadow:var(--sombra); }
  .painel h3 { margin:0 0 10px; font-size:19px; }
  .painel label.rot { display:block; font-weight:700; font-size:13px; margin:14px 0 4px; }
  .painel .dica { font-size:12px; color:var(--mut); margin:0 0 6px; }
  .painel input[type=text] { width:100%; padding:10px 14px; font-size:14px; border:1px solid var(--line); border-radius:12px; background:var(--bg); color:var(--ink); }
  .caixas { max-height:210px; overflow:auto; border:1px solid var(--line); border-radius:12px; padding:6px 12px; background:var(--bg); }
  .caixas label { display:block; font-size:13px; padding:3px 0; cursor:pointer; }
  .acoes { display:flex; flex-wrap:wrap; gap:8px; margin-top:16px; }
  .bloco { background:var(--surface); border:1px solid var(--line); border-radius:var(--raio); padding:16px 18px; margin-bottom:14px; box-shadow:var(--sombra); }
  .bloco h3 { margin:0 0 8px; font-size:17px; }
  .linha { display:flex; flex-wrap:wrap; gap:8px; align-items:center; justify-content:space-between; padding:8px 0; border-bottom:1px solid var(--line); font-size:14px; }
  .linha:last-child { border-bottom:none; }
  .bloco input[type=text], .bloco input[type=email] { padding:9px 14px; font-size:14px; border:1px solid var(--line); border-radius:999px; background:var(--bg); color:var(--ink); width:100%; max-width:340px; }
  .bloco select { padding:9px 12px; border:1px solid var(--line); border-radius:12px; background:var(--bg); color:var(--ink); margin-bottom:8px; width:100%; }
  .aviso { background:var(--surface2); border:1.5px dashed var(--amarelo2); border-radius:var(--raio); padding:14px 16px; font-size:14px; margin-bottom:14px; }
  button.mais { display:block; margin:22px auto; padding:11px 26px; border-radius:999px; border:1.5px solid var(--amarelo2); background:var(--surface); color:var(--acento); cursor:pointer; font-size:14px; font-weight:700; font-family:inherit; }
  footer { text-align:center; color:var(--mut); font-size:12px; padding:20px 20px 30px; }

  /* ---------- celular ---------- */
  @media (max-width: 860px) {
    .layout { grid-template-columns:minmax(0,1fr); gap:10px; }
    .sidebar { display:none; position:static; max-height:none; }
    .sidebar.aberta { display:block; }
    .btn-filtros { display:inline-block; }
    .marca h1 { font-size:22px; }
    .seg button { padding:8px 14px; font-size:13px; }
    .titulo { font-size:18px; }
  }
</style>
</head>
<body>
<header class="topo">
  <div class="topo-in">
    <div class="marca">
      <svg width="54" height="54" viewBox="0 0 64 64" role="img" aria-label="Logo: abelha em um favo">
        <defs><clipPath id="corpo"><ellipse cx="31" cy="37" rx="14" ry="10"/></clipPath></defs>
        <polygon points="32,3 58,18 58,46 32,61 6,46 6,18" fill="#FFC933" stroke="#E0A800" stroke-width="2" stroke-linejoin="round"/>
        <ellipse cx="22" cy="24" rx="7.5" ry="11" fill="#FFFFFF" opacity=".92" transform="rotate(-28 22 24)"/>
        <ellipse cx="36" cy="22" rx="7.5" ry="11" fill="#FFFFFF" opacity=".92" transform="rotate(18 36 22)"/>
        <ellipse cx="31" cy="37" rx="14" ry="10" fill="#2A2208"/>
        <g clip-path="url(#corpo)" fill="#FFC933"><rect x="25" y="25" width="4.5" height="24"/><rect x="34" y="25" width="4.5" height="24"/></g>
        <circle cx="46" cy="36" r="5.2" fill="#2A2208"/>
        <circle cx="47.6" cy="34.6" r="1.1" fill="#FFFFFF"/>
        <path d="M17 37 L11 38.5 L17 40 Z" fill="#2A2208"/>
      </svg>
      <div><h1>__TITULO__</h1><div class="sub">__SUBTITULO__ · atualizado em __ATUALIZADO__</div></div>
    </div>
  </div>
</header>
<div class="conta" id="conta" style="display:none"></div>

<div class="layout" id="layout">
  <aside class="sidebar" id="sidebar">
    <div class="sb-bloco" id="area-lista">
      <div class="sb-titulo">Meu perfil</div>
      <select id="perfil-sel" onchange="setPerfil(this.value)"></select>
      <div class="linha-btns">
        <button class="btn forte mini" id="btn-criar" onclick="abrirPerfil('')">+ Criar perfil</button>
        <button class="btn mini" id="btn-editar" onclick="abrirPerfil(perfilAtivo)" style="display:none">Editar</button>
      </div>
      <div class="perfil-info" id="perfil-info"></div>
    </div>
    <div id="area-filtros">
      <div id="sec-abelha"></div>
      <div id="sec-tema"></div>
      <div class="sb-bloco">
        <div class="sb-titulo">Revista</div>
        <input type="search" id="rev-busca" placeholder="Buscar revista…" oninput="setRevBusca(this.value)">
        <div class="lista-op" id="rev-list"></div>
      </div>
      <button class="btn mais-filtros" id="btn-mais" onclick="alternarMais()">Mais filtros ▾</button>
      <div id="mais-dyn"></div>
      <div id="limpar-wrap"></div>
      <div class="fnota" id="fnota"></div>
    </div>
  </aside>

  <main class="conteudo">
    <div class="barra">
      <div class="seg">
        <button class="on" id="tab-novo" onclick="setAba('novo')">Novidades</button>
        <button id="tab-classico" onclick="setAba('classico')">Clássicos</button>
        <button id="tab-salvos" onclick="setAba('salvos')" style="display:none">⭐ Salvos</button>
        <button id="tab-lab" onclick="setAba('lab')" style="display:none">👥 Laboratório</button>
      </div>
      <button class="btn btn-filtros" onclick="alternarSidebar()">☰ Filtros</button>
    </div>
    <div class="painel" id="painel" style="display:none"></div>
    <div class="busca-linha" id="area-busca">
      <input type="search" id="busca" placeholder="Buscar por palavra no título, autor ou resumo…" oninput="setBusca(this.value)">
      <select id="ordem" onchange="setOrdem(this.value)">
        <option value="padrao">Ordem padrão</option>
        <option value="sjr">Maior SJR da revista</option>
        <option value="cit">Mais citados</option>
        <option value="data">Data de publicação</option>
      </select>
    </div>
    <div class="count" id="count"></div>
    <div id="lista"></div>
    <div id="lab-view" style="display:none"></div>
    <button class="mais" id="mais" onclick="mostrarMais()" style="display:none">Mostrar mais</button>
  </main>
</div>
<footer>Montado automaticamente com dados abertos do OpenAlex e do Europe PMC. SJR: SCImago Journal Rank.</footer>
<script src="https://cdn.jsdelivr.net/npm/@supabase/supabase-js@2"></script>
<script>
const DADOS = __DADOS__;
const SB = __SUPABASE__;
const FILTROS = __FILTROS__;
const POR_PAGINA = 40;
const LS_PERFIS = 'radar_perfis_v1', LS_ATIVO = 'radar_perfil_ativo_v1';
let aba = 'novo', busca = '', limite = POR_PAGINA, editando = '';

// Junta o mesmo artigo quando ele aparece em mais de um tópico
const MAPA = {};
DADOS.forEach(d => {
  const k = d.tipo + '|' + d.key;
  if (MAPA[k]) { if (!MAPA[k].topicos.includes(d.topico)) MAPA[k].topicos.push(d.topico); }
  else MAPA[k] = Object.assign({}, d, { topicos: [d.topico] });
});
const ITENS = Object.values(MAPA);
const POR_CHAVE = {};
ITENS.forEach(d => { if (!POR_CHAVE[d.key]) POR_CHAVE[d.key] = d; });

function esc(s) {
  return String(s == null ? '' : s).replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
}
function fmtData(s) {
  if (!s) return '';
  const d = new Date(String(s).slice(0, 10) + 'T00:00:00');
  return isNaN(d) ? s : d.toLocaleDateString('pt-BR');
}
function palavras(v) { return v.split(',').map(x => x.trim().toLowerCase()).filter(Boolean); }
function erro(e) { alert('Algo deu errado: ' + ((e && e.message) || e)); }
function seguroUrl(u) { return /^https?:\/\//i.test(u || '') ? u : '#'; }

// ============================================================
//  Conta online (Supabase) — opcional
// ============================================================
let sb = null, sessao = null;
let nomeUsuario = '', perfilNuvem = null;
let meusLabs = [], labAtivo = '', membros = [], convitesLab = [];
let meusConvites = [], compartilhados = [], salvos = [];
let msgConta = '';
const nuvem = () => !!(sb && sessao);

async function iniciarConta() {
  if (!SB || !SB.url || !SB.key || !window.supabase) return;
  sb = window.supabase.createClient(SB.url, SB.key);
  document.getElementById('conta').style.display = 'flex';
  sb.auth.onAuthStateChange((ev, s) => { sessao = s; setTimeout(carregarTudo, 0); });
  const r = await sb.auth.getSession();
  sessao = r.data ? r.data.session : null;
  await carregarTudo();
}

async function carregarTudo() {
  if (!sb) return;
  if (!sessao) {
    perfilNuvem = null; nomeUsuario = ''; meusLabs = []; membros = []; convitesLab = [];
    meusConvites = []; compartilhados = []; salvos = []; labAtivo = '';
    perfis = lsGet(LS_PERFIS, {}); perfilAtivo = lsGet(LS_ATIVO, '');
    if (!perfis[perfilAtivo]) perfilAtivo = '';
    if (aba === 'salvos' || aba === 'lab') aba = 'novo';
    render(); return;
  }
  try {
    const uid = sessao.user.id;
    const email = (sessao.user.email || '').toLowerCase();
    const rp = await sb.from('perfis').select('*').eq('id', uid).maybeSingle();
    if (rp.error) throw rp.error;
    perfilNuvem = rp.data || null;
    nomeUsuario = perfilNuvem ? perfilNuvem.nome : '';
    perfis = {}; perfilAtivo = '';
    if (perfilNuvem) {
      perfis[nomeUsuario || 'Meu perfil'] = {
        topicos: perfilNuvem.topicos || [], revistas: perfilNuvem.revistas || [],
        incluir: perfilNuvem.incluir || [], excluir: perfilNuvem.excluir || [] };
      perfilAtivo = nomeUsuario || 'Meu perfil';
    }
    const rm = await sb.from('membros').select('lab_id, papel, laboratorios(id, nome, dono)').eq('user_id', uid);
    if (rm.error) throw rm.error;
    meusLabs = (rm.data || []).filter(m => m.laboratorios).map(m => ({ id: m.lab_id, nome: m.laboratorios.nome, papel: m.papel }));
    if (!meusLabs.some(l => l.id === labAtivo)) labAtivo = meusLabs.length ? meusLabs[0].id : '';
    const rc = await sb.from('convites').select('*');
    if (rc.error) throw rc.error;
    meusConvites = (rc.data || []).filter(c => (c.email || '').toLowerCase() === email);
    const rs = await sb.from('salvos').select('*').order('criado_em', { ascending: false });
    if (rs.error) throw rs.error;
    salvos = rs.data || [];
    await carregarLab();
  } catch (e) { erro(e); }
  render();
  if (!perfilNuvem && !document.getElementById('painel').innerHTML) abrirPerfil('');
}

async function carregarLab() {
  membros = []; convitesLab = []; compartilhados = [];
  if (!nuvem() || !labAtivo) return;
  const rm = await sb.from('membros').select('user_id, papel').eq('lab_id', labAtivo);
  if (rm.error) throw rm.error;
  const ids = (rm.data || []).map(m => m.user_id);
  let nomes = {};
  if (ids.length) {
    const rp = await sb.from('perfis').select('id, nome').in('id', ids);
    if (rp.error) throw rp.error;
    (rp.data || []).forEach(p => { nomes[p.id] = p.nome; });
  }
  membros = (rm.data || []).map(m => ({ user_id: m.user_id, papel: m.papel, nome: nomes[m.user_id] || '(sem nome)' }));
  const rs = await sb.from('compartilhados').select('*').eq('lab_id', labAtivo).order('criado_em', { ascending: false });
  if (rs.error) throw rs.error;
  compartilhados = rs.data || [];
  if (souDono()) {
    const rc = await sb.from('convites').select('*').eq('lab_id', labAtivo);
    if (rc.error) throw rc.error;
    convitesLab = rc.data || [];
  }
}
const labAtual = () => meusLabs.find(l => l.id === labAtivo) || null;
const souDono = () => { const l = labAtual(); return !!(l && l.papel === 'dono'); };
const meuId = () => (sessao && sessao.user ? sessao.user.id : '');
const nomeDe = uid => { const m = membros.find(x => x.user_id === uid); return m ? m.nome : '(alguém)'; };

async function entrarPorEmail() {
  const el = document.getElementById('c-email');
  const email = (el.value || '').trim();
  if (!/^[^@\s]+@[^@\s]+\.[^@\s]+$/.test(email)) { alert('Digite um e-mail válido.'); return; }
  const r = await sb.auth.signInWithOtp({ email, options: { emailRedirectTo: location.origin + location.pathname } });
  if (r.error) { erro(r.error); return; }
  msgConta = 'Enviamos um link de acesso para ' + email + '. Abra o e-mail e clique no link (veja também o spam).';
  renderConta();
}
async function sair() { await sb.auth.signOut(); }

function renderConta() {
  const c = document.getElementById('conta');
  if (!sb) { c.style.display = 'none'; return; }
  c.style.display = 'flex';
  if (!sessao) {
    c.innerHTML = '<b>Entrar</b>' +
      '<input type="email" id="c-email" placeholder="seu e-mail" onkeydown="if(event.key===\'Enter\')entrarPorEmail()">' +
      '<button class="btn forte" onclick="entrarPorEmail()">Receber link de acesso</button>' +
      '<div class="msg">' + esc(msgConta || 'Sem senha: enviamos um link para o seu e-mail. Entrando, seu perfil, seus salvos e o seu laboratório ficam disponíveis em qualquer aparelho.') + '</div>';
  } else {
    const n = meusConvites.length;
    c.innerHTML = '<span>👋 Olá, <b>' + esc(nomeUsuario || sessao.user.email) + '</b></span>' +
      (n ? '<button class="btn forte mini" onclick="setAba(\'lab\')">📩 ' + n + ' convite(s) de laboratório</button>' : '') +
      '<span style="flex:1"></span><button class="btn mini" onclick="sair()">Sair</button>';
  }
}

// ============================================================
//  Perfis (na nuvem quando logado; no navegador caso contrário)
// ============================================================
function lsGet(k, def) { try { const v = localStorage.getItem(k); return v ? JSON.parse(v) : def; } catch (e) { return def; } }
function lsSet(k, v) { try { localStorage.setItem(k, JSON.stringify(v)); } catch (e) {} }
let perfis = lsGet(LS_PERFIS, {});
let perfilAtivo = lsGet(LS_ATIVO, '');
if (!perfis[perfilAtivo]) perfilAtivo = '';
function salvarLocal() { if (!nuvem()) { lsSet(LS_PERFIS, perfis); lsSet(LS_ATIVO, perfilAtivo); } }

function passaPerfil(d) {
  const p = perfis[perfilAtivo];
  if (!p) return true;
  if (p.topicos.length && !d.topicos.some(t => p.topicos.includes(t))) return false;
  if (p.revistas.length && !p.revistas.includes(d.revista)) return false;
  const txt = (d.titulo + ' ' + d.autores + ' ' + d.resumo + ' ' + d.revista).toLowerCase();
  if (p.incluir.length && !p.incluir.some(w => txt.includes(w))) return false;
  if (p.excluir.some(w => txt.includes(w))) return false;
  return true;
}
function topicosVisiveis(d) {
  const p = perfis[perfilAtivo];
  return (p && p.topicos.length) ? d.topicos.filter(t => p.topicos.includes(t)) : d.topicos;
}
function setPerfil(nome) {
  perfilAtivo = perfis[nome] ? nome : '';
  salvarLocal(); fecharPainel(); resetarSel(); limite = POR_PAGINA; render();
}

function renderPerfilBar() {
  const sel = document.getElementById('perfil-sel');
  sel.innerHTML = '<option value="">Todos os artigos (sem perfil)</option>' +
    Object.keys(perfis).sort().map(n => '<option value="' + esc(n) + '">' + esc(n) + '</option>').join('');
  sel.value = perfilAtivo;
  const jaTem = nuvem() && !!perfilNuvem;
  document.getElementById('btn-criar').style.display = jaTem ? 'none' : 'inline-block';
  document.getElementById('btn-criar').textContent = nuvem() ? '+ Criar meu perfil' : '+ Criar meu perfil';
  document.getElementById('btn-editar').style.display = perfilAtivo ? 'inline-block' : 'none';
  const p = perfis[perfilAtivo];
  document.getElementById('perfil-info').textContent = p
    ? 'Perfil ativo: ' + (p.topicos.length ? p.topicos.length + ' tópico(s)' : 'todos os tópicos') + ' · ' +
      (p.revistas.length ? p.revistas.length + ' revista(s)' : 'qualquer revista') +
      (p.incluir.length ? ' · só com: ' + p.incluir.join(', ') : '') +
      (p.excluir.length ? ' · escondendo: ' + p.excluir.join(', ') : '')
    : 'Crie um perfil para ver só os temas e revistas do seu interesse.';
}

function abrirPerfil(nome) {
  const p = (nome && perfis[nome]) ? perfis[nome] : { topicos: [], revistas: [], incluir: [], excluir: [] };
  editando = (nome && perfis[nome]) ? nome : '';
  const topicosTodos = [...new Set(ITENS.flatMap(d => d.topicos))].sort();
  const cont = {};
  ITENS.forEach(d => { if (d.revista) cont[d.revista] = (cont[d.revista] || 0) + 1; });
  const revistasTodas = Object.keys(cont).sort((a, b) => cont[b] - cont[a]).slice(0, 400);
  p.revistas.forEach(r => { if (!revistasTodas.includes(r)) revistasTodas.push(r); });
  const nomeSugerido = editando || nomeUsuario || '';
  const html =
    '<h3>' + (editando ? 'Editar perfil' : 'Criar perfil') + '</h3>' +
    '<label class="rot" for="p-nome">Nome do perfil' + (nuvem() ? ' (é como seus colegas vão ver você)' : '') + '</label>' +
    '<input type="text" id="p-nome" placeholder="Ex.: Ana" value="' + esc(nomeSugerido) + '">' +
    '<label class="rot">Tópicos que me interessam</label>' +
    '<div class="dica">Marque os que quiser. Se não marcar nenhum, aparecem todos.</div>' +
    '<div class="caixas">' + topicosTodos.map(t =>
      '<label><input type="checkbox" class="ck-top" value="' + esc(t) + '"' + (p.topicos.includes(t) ? ' checked' : '') + '> ' + esc(t) + '</label>').join('') + '</div>' +
    '<label class="rot">Revistas</label>' +
    '<div class="dica">Marque as revistas que quer ver. Se não marcar nenhuma, aparecem todas. Use a busca para achar uma revista.</div>' +
    '<input type="text" id="p-busca-rev" placeholder="Buscar revista…" oninput="filtrarListaRevistas(this.value)" style="margin-bottom:6px">' +
    '<div class="caixas" id="lista-rev">' + revistasTodas.map(r =>
      '<label class="rev-item" data-n="' + esc(r.toLowerCase()) + '"><input type="checkbox" class="ck-rev" value="' + esc(r) + '"' +
      (p.revistas.includes(r) ? ' checked' : '') + '> ' + esc(r) + ' <span style="color:var(--mut)">(' + (cont[r] || 0) + ')</span></label>').join('') + '</div>' +
    '<label class="rot" for="p-inc">Só mostrar artigos que contenham (opcional)</label>' +
    '<div class="dica">Palavras em inglês, separadas por vírgula. Aparece se tiver QUALQUER uma delas. Ex.: nest, foraging</div>' +
    '<input type="text" id="p-inc" value="' + esc(p.incluir.join(', ')) + '">' +
    '<label class="rot" for="p-exc">Esconder artigos que contenham (opcional)</label>' +
    '<div class="dica">Palavras separadas por vírgula. Ex.: genome, review</div>' +
    '<input type="text" id="p-exc" value="' + esc(p.excluir.join(', ')) + '">' +
    '<div class="dica" style="margin-top:12px">' + (nuvem()
      ? 'Seu perfil fica salvo na sua conta e acompanha você em qualquer aparelho.'
      : 'Sem entrar na conta, o perfil fica salvo só neste navegador. Para usar em outro aparelho, entre com seu e-mail ou use "Copiar link do perfil".') + '</div>' +
    '<div class="acoes">' +
      '<button class="btn forte" onclick="salvarPerfil()">Salvar perfil</button>' +
      (nuvem() ? '' : '<button class="btn" onclick="copiarLink()">Copiar link do perfil</button>') +
      '<button class="btn" onclick="fecharPainel()">Cancelar</button>' +
      (editando ? '<button class="btn perigo" onclick="apagarPerfil()">Apagar perfil</button>' : '') +
    '</div>';
  const painel = document.getElementById('painel');
  painel.innerHTML = html;
  painel.style.display = 'block';
  if (painel.scrollIntoView) painel.scrollIntoView({ behavior: 'smooth', block: 'start' });
}
function fecharPainel() { const p = document.getElementById('painel'); p.style.display = 'none'; p.innerHTML = ''; }
function filtrarListaRevistas(v) {
  v = v.toLowerCase().trim();
  document.querySelectorAll('.rev-item').forEach(el => { el.style.display = (!v || el.dataset.n.includes(v)) ? 'block' : 'none'; });
}
function lerFormulario() {
  return {
    nome: document.getElementById('p-nome').value.trim(),
    topicos: [...document.querySelectorAll('.ck-top:checked')].map(e => e.value),
    revistas: [...document.querySelectorAll('.ck-rev:checked')].map(e => e.value),
    incluir: palavras(document.getElementById('p-inc').value),
    excluir: palavras(document.getElementById('p-exc').value)
  };
}
async function salvarPerfil() {
  const f = lerFormulario();
  if (!f.nome) { alert('Dê um nome ao perfil (por exemplo, o seu nome).'); return; }
  if (nuvem()) {
    const r = await sb.from('perfis').upsert({ id: meuId(), nome: f.nome, topicos: f.topicos, revistas: f.revistas,
      incluir: f.incluir, excluir: f.excluir, atualizado_em: new Date().toISOString() });
    if (r.error) { erro(r.error); return; }
    fecharPainel(); resetarSel(); limite = POR_PAGINA;
    await carregarTudo(); return;
  }
  if (editando && editando !== f.nome) delete perfis[editando];
  perfis[f.nome] = { topicos: f.topicos, revistas: f.revistas, incluir: f.incluir, excluir: f.excluir };
  perfilAtivo = f.nome;
  salvarLocal(); fecharPainel(); resetarSel(); limite = POR_PAGINA; render();
}
async function apagarPerfil() {
  if (!editando || !confirm('Apagar o perfil "' + editando + '"?')) return;
  if (nuvem()) {
    const r = await sb.from('perfis').delete().eq('id', meuId());
    if (r.error) { erro(r.error); return; }
    fecharPainel(); await carregarTudo(); return;
  }
  delete perfis[editando]; perfilAtivo = '';
  salvarLocal(); fecharPainel(); render();
}
function copiarLink() {
  const f = lerFormulario();
  if (!f.nome) { alert('Dê um nome ao perfil antes de copiar o link.'); return; }
  const b64 = btoa(unescape(encodeURIComponent(JSON.stringify(f)))).replace(/\+/g, '-').replace(/\//g, '_');
  const link = location.origin + location.pathname + '#perfil=' + b64;
  if (navigator.clipboard && navigator.clipboard.writeText) {
    navigator.clipboard.writeText(link).then(() => alert('Link copiado! Quem abrir poderá adicionar este perfil.'),
      () => prompt('Copie o link:', link));
  } else { prompt('Copie o link:', link); }
}
function importarDoLink() {
  const m = location.hash.match(/^#perfil=(.+)$/);
  if (!m) return;
  try {
    const p = JSON.parse(decodeURIComponent(escape(atob(m[1].replace(/-/g, '+').replace(/_/g, '/')))));
    if (p && p.nome && confirm('Adicionar o perfil "' + p.nome + '" neste navegador?')) {
      perfis[p.nome] = { topicos: p.topicos || [], revistas: p.revistas || [], incluir: p.incluir || [], excluir: p.excluir || [] };
      perfilAtivo = p.nome; salvarLocal();
    }
  } catch (e) {}
  history.replaceState(null, '', location.pathname + location.search);
}

// ============================================================
//  Salvos e compartilhamento
// ============================================================
const estaSalvo = k => salvos.some(s => s.chave === k);
function snapshot(d) {
  return { titulo: d.titulo, url: d.url, revista: d.revista || null, ano: d.ano || null, resumo: (d.resumo || '').slice(0, 600) };
}
async function alternarSalvo(k) {
  const d = POR_CHAVE[k]; if (!d || !nuvem()) return;
  if (estaSalvo(k)) {
    const r = await sb.from('salvos').delete().eq('user_id', meuId()).eq('chave', k);
    if (r.error) { erro(r.error); return; }
  } else {
    const r = await sb.from('salvos').upsert(Object.assign({ user_id: meuId(), chave: k }, snapshot(d)));
    if (r.error) { erro(r.error); return; }
  }
  const rs = await sb.from('salvos').select('*').order('criado_em', { ascending: false });
  salvos = rs.data || []; render();
}
async function removerSalvo(k) {
  const r = await sb.from('salvos').delete().eq('user_id', meuId()).eq('chave', k);
  if (r.error) { erro(r.error); return; }
  salvos = salvos.filter(s => s.chave !== k); render();
}
async function compartilhar(k) {
  const d = POR_CHAVE[k]; const lab = labAtual();
  if (!d || !lab) { alert('Entre em um laboratório primeiro (aba Laboratório).'); return; }
  const nota = prompt('Compartilhar com "' + lab.nome + '".\nNota para o laboratório (opcional):', '');
  if (nota === null) return;
  const r = await sb.from('compartilhados').insert(Object.assign(
    { lab_id: lab.id, user_id: meuId(), chave: k, nota: nota.trim() || null }, snapshot(d)));
  if (r.error) {
    if (r.error.code === '23505') alert('Este artigo já foi compartilhado com o laboratório.');
    else erro(r.error);
    return;
  }
  await carregarLab(); alert('Compartilhado com ' + lab.nome + '!'); render();
}
async function removerCompartilhado(id) {
  if (!confirm('Remover este artigo da página do laboratório?')) return;
  const r = await sb.from('compartilhados').delete().eq('id', id);
  if (r.error) { erro(r.error); return; }
  compartilhados = compartilhados.filter(c => c.id !== id); render();
}

// ============================================================
//  Laboratório
// ============================================================
async function criarLab() {
  const nome = (document.getElementById('lab-nome').value || '').trim();
  if (!nome) { alert('Dê um nome ao laboratório.'); return; }
  const r = await sb.rpc('criar_laboratorio', { p_nome: nome });
  if (r.error) { erro(r.error); return; }
  labAtivo = r.data; await carregarTudo();
}
async function trocarLab(id) { labAtivo = id; try { await carregarLab(); } catch (e) { erro(e); } render(); }
async function convidar() {
  const el = document.getElementById('lab-convite');
  const email = (el.value || '').trim();
  if (!email) { alert('Digite o e-mail da pessoa.'); return; }
  const r = await sb.rpc('convidar', { p_lab: labAtivo, p_email: email });
  if (r.error) { erro(r.error); return; }
  const lab = labAtual();
  const texto = 'Oi! Te convidei para o laboratório "' + lab.nome + '" no Radar de Abelhas.\nAbra ' +
    location.origin + location.pathname + ' , entre com o e-mail ' + email.toLowerCase() +
    ' (você recebe um link de acesso) e aceite o convite na aba Laboratório.';
  try { await carregarLab(); } catch (e) { erro(e); }
  render();
  prompt('Convite criado! Copie esta mensagem e envie para a pessoa (por WhatsApp ou e-mail):', texto);
}
async function cancelarConvite(id) {
  const r = await sb.from('convites').delete().eq('id', id);
  if (r.error) { erro(r.error); return; }
  convitesLab = convitesLab.filter(c => c.id !== id);
  meusConvites = meusConvites.filter(c => c.id !== id); render();
}
async function aceitarConvite(id) {
  const r = await sb.rpc('aceitar_convite', { p_convite: id });
  if (r.error) { erro(r.error); return; }
  labAtivo = r.data; await carregarTudo();
}
async function removerMembro(uid) {
  if (!confirm('Remover ' + nomeDe(uid) + ' do laboratório?')) return;
  const r = await sb.from('membros').delete().eq('lab_id', labAtivo).eq('user_id', uid);
  if (r.error) { erro(r.error); return; }
  try { await carregarLab(); } catch (e) { erro(e); } render();
}
async function sairDoLab() {
  const lab = labAtual();
  if (!lab || !confirm('Sair do laboratório "' + lab.nome + '"?')) return;
  const r = await sb.from('membros').delete().eq('lab_id', labAtivo).eq('user_id', meuId());
  if (r.error) { erro(r.error); return; }
  labAtivo = ''; await carregarTudo();
}

function cardSimples(r, extra) {
  return '<article class="card"><div class="card-top"><div class="rv">' +
    (r.revista ? '<span class="rev">' + esc(r.revista) + '</span>' : '<span class="rev mut">Revista não informada</span>') +
    '</div><span class="data">' + esc(r.ano || '') + '</span></div>' +
    '<a class="titulo" href="' + esc(seguroUrl(r.url)) + '" target="_blank" rel="noopener">' + esc(r.titulo) + '</a>' +
    (r.resumo ? '<details class="det"><summary>Resumo</summary><div class="det-in"><div class="res">' + esc(r.resumo) + '</div></div></details>' : '') +
    (extra || '') + '</article>';
}

function renderLab() {
  const v = document.getElementById('lab-view');
  let h = '';
  if (meusConvites.length) {
    h += '<div class="aviso"><b>📩 Convites para você</b>' + meusConvites.map(c =>
      '<div class="linha"><span>Laboratório <b>' + esc(c.lab_nome) + '</b></span><span>' +
      '<button class="btn forte mini" onclick="aceitarConvite(\'' + esc(c.id) + '\')">Aceitar</button> ' +
      '<button class="btn mini" onclick="cancelarConvite(\'' + esc(c.id) + '\')">Recusar</button></span></div>').join('') + '</div>';
  }
  const lab = labAtual();
  if (!lab) {
    h += '<div class="bloco"><h3>Criar um laboratório</h3>' +
      '<p style="font-size:13px;color:var(--mut);margin-top:0">Você será o dono e poderá convidar as pessoas do seu grupo pelo e-mail.</p>' +
      '<input type="text" id="lab-nome" placeholder="Nome do laboratório"> ' +
      '<button class="btn forte" onclick="criarLab()">Criar laboratório</button></div>';
    v.innerHTML = h; return;
  }
  h += '<div class="bloco"><h3>👥 ' + esc(lab.nome) + '</h3>';
  if (meusLabs.length > 1) {
    h += '<select onchange="trocarLab(this.value)">' + meusLabs.map(l =>
      '<option value="' + esc(l.id) + '"' + (l.id === labAtivo ? ' selected' : '') + '>' + esc(l.nome) + '</option>').join('') + '</select>';
  }
  h += '<div style="font-size:13px;color:var(--mut);margin-bottom:6px">Integrantes</div>' +
    membros.map(m => '<div class="linha"><span>' + esc(m.nome) + (m.papel === 'dono' ? ' <span class="tag">dono</span>' : '') +
      (m.user_id === meuId() ? ' <span class="tag">você</span>' : '') + '</span>' +
      (souDono() && m.user_id !== meuId() ? '<button class="btn perigo mini" onclick="removerMembro(\'' + esc(m.user_id) + '\')">Remover</button>' : '') +
      '</div>').join('');
  if (souDono()) {
    h += '<div style="margin-top:12px;font-size:13px;color:var(--mut)">Convidar pessoa</div>' +
      '<div style="display:flex;gap:8px;flex-wrap:wrap"><input type="email" id="lab-convite" placeholder="e-mail da pessoa"> ' +
      '<button class="btn forte" onclick="convidar()">Convidar</button></div>';
    if (convitesLab.length) {
      h += '<div style="margin-top:10px;font-size:13px;color:var(--mut)">Convites pendentes</div>' + convitesLab.map(c =>
        '<div class="linha"><span>' + esc(c.email) + '</span><button class="btn mini" onclick="cancelarConvite(\'' + esc(c.id) + '\')">Cancelar</button></div>').join('');
    }
  } else {
    h += '<div class="acoes"><button class="btn perigo mini" onclick="sairDoLab()">Sair do laboratório</button></div>';
  }
  h += '</div>';
  h += '<div class="bloco"><h3>📌 Compartilhados no laboratório (' + compartilhados.length + ')</h3>' +
    '<div style="font-size:12px;color:var(--mut)">Nas abas Novidades e Clássicos, use "👥 Compartilhar" em um artigo para ele aparecer aqui para todo o grupo.</div></div>';
  h += compartilhados.map(c => {
    const pode = c.user_id === meuId() || souDono();
    const extra = '<div class="meta">Compartilhado por <b>' + esc(nomeDe(c.user_id)) + '</b> em ' + fmtData(c.criado_em) + '</div>' +
      (c.nota ? '<div class="nota">💬 ' + esc(c.nota) + '</div>' : '') +
      (pode ? '<div class="botoes"><button class="btn mini perigo" onclick="removerCompartilhado(\'' + esc(c.id) + '\')">Remover</button></div>' : '');
    return cardSimples(c, extra);
  }).join('');
  v.innerHTML = h;
}

// ============================================================
//  Lista de artigos e filtros
// ============================================================
let topicosSel = [], revistasSel = [], fac = {};
let periodo = '', quartil = '', ordem = 'padrao', revBusca = '', maisAberto = false;
function resetarSel() { topicosSel = []; revistasSel = []; }
const TEM_SJR = ITENS.some(d => d.sjr != null);
const textoDe = d => (d.titulo + ' ' + d.autores + ' ' + d.resumo + ' ' + d.revista).toLowerCase();
const anoDe = d => d.ano || parseInt((d.data || '').slice(0, 4), 10) || 0;
const opcoesDe = (d, nome) => (d.facetas && d.facetas[nome]) || [];
function passaPeriodo(d) {
  if (!periodo) return true;
  const a = anoDe(d), atual = new Date().getFullYear();
  if (!a) return false;
  if (periodo === '5') return a >= atual - 5;
  if (periodo === '10') return a >= atual - 10;
  if (periodo === '2020+') return a >= 2020;
  if (periodo === '2010-2019') return a >= 2010 && a <= 2019;
  if (periodo === '2000-2009') return a >= 2000 && a <= 2009;
  if (periodo === 'antes2000') return a < 2000;
  return true;
}
function passaQuartil(d) {
  if (!quartil) return true;
  const q = d.q || '';
  if (quartil === 'sem') return !q;
  if (quartil === 'Q1') return q === 'Q1';
  if (quartil === 'Q12') return q === 'Q1' || q === 'Q2';
  if (quartil === 'Q123') return ['Q1', 'Q2', 'Q3'].includes(q);
  return true;
}
function setAba(a) { aba = a; limite = POR_PAGINA; render(); }
function setBusca(v) { busca = v.toLowerCase().trim(); limite = POR_PAGINA; render(); }
function setOrdem(v) { ordem = v; limite = POR_PAGINA; render(); }
function setPeriodo(v) { periodo = v; limite = POR_PAGINA; render(); }
function setQuartil(v) { quartil = v; limite = POR_PAGINA; render(); }
function setRevBusca(v) { revBusca = v.toLowerCase().trim(); render(); }
function alternarMais() { maisAberto = !maisAberto; render(); }
function alternarSidebar() { document.getElementById('sidebar').classList.toggle('aberta'); }
function alternarSel(arr, v) { const k = arr.indexOf(v); if (k >= 0) arr.splice(k, 1); else arr.push(v); }
function limparFiltros() {
  resetarSel(); fac = {}; periodo = ''; quartil = ''; busca = ''; revBusca = '';
  document.getElementById('busca').value = ''; document.getElementById('rev-busca').value = '';
  limite = POR_PAGINA; render();
}
function mostrarMais() { limite += POR_PAGINA; render(); }
function fmtSjr(v) { return (Math.round(v * 100) / 100).toFixed(2); }

function cabecalhoCard(d, dataTxt) {
  const sjr = d.sjr != null
    ? '<span class="sjr" title="SCImago Journal Rank (SJR) da revista">SJR ' + fmtSjr(d.sjr) + (d.q ? ' · ' + esc(d.q) : '') + '</span>' : '';
  return '<div class="card-top"><div class="rv">' +
    (d.revista ? '<span class="rev">' + esc(d.revista) + '</span>' : '<span class="rev mut">Revista não informada</span>') + sjr +
    '</div><span class="data">' + esc(dataTxt) + '</span></div>';
}
function itemHtml(d) {
  const dataTxt = aba === 'classico'
    ? [d.ano || fmtData(d.data), (d.citacoes || 0) + ' citações'].filter(Boolean).join(' · ')
    : (fmtData(d.data) || String(d.ano || ''));
  const tags = topicosVisiveis(d).map(t => '<span class="tag">' + esc(t) + '</span>').join('');
  let botoes = '';
  if (nuvem()) {
    botoes = '<div class="botoes"><button class="btn mini" data-acao="salvar" data-k="' + esc(d.key) + '">' +
      (estaSalvo(d.key) ? '⭐ Salvo' : '☆ Salvar') + '</button>' +
      (labAtual() ? '<button class="btn mini" data-acao="compartilhar" data-k="' + esc(d.key) + '">👥 Compartilhar com o lab</button>' : '') + '</div>';
  }
  return '<article class="card">' + cabecalhoCard(d, dataTxt) +
    '<a class="titulo" href="' + esc(seguroUrl(d.url)) + '" target="_blank" rel="noopener">' + esc(d.titulo) + '</a>' +
    '<div class="autores">' + esc(d.autores) + '</div>' +
    '<details class="det"><summary>Resumo e detalhes</summary><div class="det-in"><div class="tags">' + tags + '</div>' +
    '<div class="res">' + (d.resumo ? esc(d.resumo) : '<i>(sem resumo disponível)</i>') + '</div></div></details>' + botoes + '</article>';
}

function checks(itens, tipo, f) {
  return itens.map(o => '<label class="op' + (o.n === 0 && !o.on ? ' zero' : '') + '"><input type="checkbox" data-tipo="' + tipo +
    '" data-f="' + esc(f || '') + '" data-o="' + esc(o.nome) + '"' + (o.on ? ' checked' : '') + '><span class="ck"></span>' +
    '<span class="nome">' + esc(o.nome) + '</span><span class="n">' + o.n + '</span></label>').join('');
}
function ordenar(xs) {
  const padrao = (a, b) => aba === 'novo'
    ? ((b.adicionado || '').localeCompare(a.adicionado || '') || (b.data || '').localeCompare(a.data || ''))
    : ((b.citacoes || 0) - (a.citacoes || 0));
  const o = ordem === 'padrao' ? 'padrao' : ordem;
  return xs.slice().sort((a, b) => {
    if (o === 'sjr') return ((b.sjr != null ? b.sjr : -1) - (a.sjr != null ? a.sjr : -1)) || padrao(a, b);
    if (o === 'cit') return ((b.citacoes || 0) - (a.citacoes || 0)) || padrao(a, b);
    if (o === 'data') return ((b.data || String(b.ano || '')).localeCompare(a.data || String(a.ano || ''))) || padrao(a, b);
    return padrao(a, b);
  });
}

function render() {
  renderConta();
  const logado = nuvem();
  document.getElementById('tab-salvos').style.display = logado ? 'inline-block' : 'none';
  document.getElementById('tab-lab').style.display = logado ? 'inline-block' : 'none';
  const ehLab = aba === 'lab', ehSalvos = aba === 'salvos';
  ['novo', 'classico', 'salvos', 'lab'].forEach(x => document.getElementById('tab-' + x).classList.toggle('on', aba === x));
  document.getElementById('lab-view').style.display = ehLab ? 'block' : 'none';
  document.getElementById('layout').classList.toggle('sem-sidebar', ehLab || ehSalvos);
  document.getElementById('area-busca').style.display = (ehLab || ehSalvos) ? 'none' : 'flex';
  if (!(ehLab || ehSalvos)) renderPerfilBar();

  if (ehLab) {
    document.getElementById('lista').innerHTML = '';
    document.getElementById('count').textContent = '';
    document.getElementById('mais').style.display = 'none';
    renderLab(); return;
  }
  if (ehSalvos) {
    document.getElementById('count').textContent = salvos.length + ' artigo(s) salvo(s)';
    document.getElementById('lista').innerHTML = salvos.length ? salvos.map(s =>
      cardSimples(s, '<div class="botoes"><button class="btn mini" data-acao="remover-salvo" data-k="' + esc(s.chave) + '">Remover dos salvos</button>' +
      (labAtual() && POR_CHAVE[s.chave] ? '<button class="btn mini" data-acao="compartilhar" data-k="' + esc(s.chave) + '">👥 Compartilhar com o lab</button>' : '') + '</div>')).join('')
      : '<p style="color:var(--mut)">Você ainda não salvou nada. Use "☆ Salvar" nos artigos.</p>';
    document.getElementById('mais').style.display = 'none';
    return;
  }

  // ---- filtros em cascata: cada contagem respeita os outros filtros ----
  const base = ITENS.filter(d => d.tipo === aba && passaPerfil(d));
  const todosT = [...new Set(base.flatMap(topicosVisiveis))].sort();
  topicosSel = topicosSel.filter(t => todosT.includes(t));
  const passaTudo = (d, ig) => {
    if (ig !== 'topico' && topicosSel.length && !d.topicos.some(t => topicosSel.includes(t))) return false;
    if (ig !== 'rev' && revistasSel.length && !revistasSel.includes(d.revista)) return false;
    if (ig !== 'periodo' && !passaPeriodo(d)) return false;
    if (ig !== 'quartil' && !passaQuartil(d)) return false;
    for (const f of FILTROS) {
      const sel = fac[f.nome];
      if (ig !== 'f:' + f.nome && sel && sel.length && !opcoesDe(d, f.nome).some(o => sel.includes(o))) return false;
    }
    if (busca && !textoDe(d).includes(busca)) return false;
    return true;
  };
  const filtrar = ig => base.filter(d => passaTudo(d, ig));
  const secao = (titulo, corpo) => '<div class="sb-bloco"><div class="sb-titulo">' + esc(titulo) + '</div>' + corpo + '</div>';
  const facetaHtml = f => {
    const arr = filtrar('f:' + f.nome), sel = fac[f.nome] || [];
    return secao(f.nome, '<div class="lista-op">' + checks(f.opcoes.map(o => ({
      nome: o, n: arr.filter(d => opcoesDe(d, f.nome).includes(o)).length, on: sel.includes(o) })), 'faceta', f.nome) + '</div>');
  };

  // Abelha (primeira categoria) e Tema
  document.getElementById('sec-abelha').innerHTML = FILTROS.length ? facetaHtml(FILTROS[0]) : '';
  const arrT = filtrar('topico'), contT = {};
  arrT.forEach(d => topicosVisiveis(d).forEach(t => { contT[t] = (contT[t] || 0) + 1; }));
  document.getElementById('sec-tema').innerHTML = secao('Tema', '<div class="lista-op">' +
    checks(todosT.map(t => ({ nome: t, n: contT[t] || 0, on: topicosSel.includes(t) })), 'topico') + '</div>');

  // Revista
  const arrR = filtrar('rev'), contR = {};
  arrR.forEach(d => { if (d.revista) contR[d.revista] = (contR[d.revista] || 0) + 1; });
  const revs = Object.keys(contR).sort((a, b) => contR[b] - contR[a]);
  revistasSel.forEach(r => { if (!revs.includes(r)) revs.push(r); });
  const revsVis = revs.filter(r => !revBusca || r.toLowerCase().includes(revBusca) || revistasSel.includes(r)).slice(0, 300);
  document.getElementById('rev-list').innerHTML = revsVis.length
    ? checks(revsVis.map(r => ({ nome: r, n: contR[r] || 0, on: revistasSel.includes(r) })), 'rev')
    : '<div class="dica" style="font-size:12px;color:var(--mut)">Nenhuma revista encontrada.</div>';

  // Mais filtros (demais categorias, período, quartil da revista)
  document.getElementById('btn-mais').textContent = maisAberto ? 'Menos filtros ▴' : 'Mais filtros ▾';
  let mais = '';
  if (maisAberto) {
    mais = FILTROS.slice(1).map(facetaHtml).join('') +
      secao('Período', '<select onchange="setPeriodo(this.value)">' +
        [['', 'Qualquer ano'], ['5', 'Últimos 5 anos'], ['10', 'Últimos 10 anos'], ['2020+', '2020 em diante'],
         ['2010-2019', '2010 a 2019'], ['2000-2009', '2000 a 2009'], ['antes2000', 'Antes de 2000']]
          .map(p => '<option value="' + p[0] + '"' + (periodo === p[0] ? ' selected' : '') + '>' + p[1] + '</option>').join('') + '</select>') +
      (TEM_SJR ? secao('Qualidade da revista (SJR)', '<select onchange="setQuartil(this.value)">' +
        [['', 'Qualquer'], ['Q1', 'Só Q1'], ['Q12', 'Q1 ou Q2'], ['Q123', 'Q1, Q2 ou Q3'], ['sem', 'Sem dado de SJR']]
          .map(p => '<option value="' + p[0] + '"' + (quartil === p[0] ? ' selected' : '') + '>' + p[1] + '</option>').join('') + '</select>') : '');
  }
  document.getElementById('mais-dyn').innerHTML = mais;
  const ativos = !!(topicosSel.length || revistasSel.length || periodo || quartil || busca || Object.values(fac).some(s => s && s.length));
  document.getElementById('limpar-wrap').innerHTML = ativos
    ? '<button class="btn perigo largo" style="margin-bottom:14px" onclick="limparFiltros()">✖ Limpar todos os filtros</button>' : '';
  document.getElementById('fnota').textContent = FILTROS.length
    ? 'As categorias são detectadas automaticamente por palavras no título e no resumo e podem ter erros. Os números mostram quantos artigos sobram com os outros filtros aplicados.' : '';
  document.getElementById('ordem').value = ordem;

  // Lista
  const xs = ordenar(filtrar(''));
  document.getElementById('count').textContent = xs.length + ' artigo(s)' + (ativos ? ' com os filtros escolhidos' : '');
  const parte = xs.slice(0, limite);
  let out = '', diaAtual = null;
  for (const d of parte) {
    if (aba === 'novo' && ordem === 'padrao' && d.adicionado !== diaAtual) {
      diaAtual = d.adicionado;
      out += '<h2 class="dia">Chegaram em ' + fmtData(diaAtual) + '</h2>';
    }
    out += itemHtml(d);
  }
  if (!parte.length) out = '<p style="color:var(--mut)">Nada encontrado com esses filtros.</p>';
  document.getElementById('lista').innerHTML = out;
  document.getElementById('mais').style.display = xs.length > limite ? 'block' : 'none';
}

document.getElementById('sidebar').addEventListener('change', ev => {
  const i = ev.target;
  if (!i.matches || !i.matches('input[type=checkbox][data-tipo]')) return;
  const tp = i.dataset.tipo, o = i.dataset.o;
  limite = POR_PAGINA;
  if (tp === 'topico') alternarSel(topicosSel, o);
  else if (tp === 'rev') alternarSel(revistasSel, o);
  else if (tp === 'faceta') { const f = i.dataset.f; if (!fac[f]) fac[f] = []; alternarSel(fac[f], o); }
  render();
});

document.getElementById('lista').addEventListener('click', ev => {
  const b = ev.target.closest('button[data-acao]'); if (!b) return;
  const k = b.dataset.k;
  if (b.dataset.acao === 'salvar') alternarSalvo(k);
  else if (b.dataset.acao === 'compartilhar') compartilhar(k);
  else if (b.dataset.acao === 'remover-salvo') removerSalvo(k);
});

importarDoLink();
render();
iniciarConta();
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
    comp = compilar_facetas(cfg)
    for d in itens:
        if not d.get("facetas"):
            d["facetas"] = classificar(d.get("titulo"), d.get("resumo"), comp)
    por_issn, por_titulo = carregar_sjr(cfg)
    saida = []
    for d in itens:
        x = {k: v for k, v in d.items() if k != "issn"}
        hit = sjr_de(d, por_issn, por_titulo)
        x["sjr"], x["q"] = (hit[0], hit[1]) if hit else (None, "")
        saida.append(x)
    dados = json.dumps(saida, ensure_ascii=False).replace("</", "<\\/")
    filtros_json = json.dumps(definicao_filtros(cfg), ensure_ascii=False).replace("</", "<\\/")
    site = cfg.get("site", {})
    sbc = cfg.get("supabase") or {}
    if sbc.get("url") and sbc.get("anon_key"):
        supabase_json = json.dumps({"url": sbc["url"].strip(), "key": sbc["anon_key"].strip()})
    else:
        supabase_json = "null"
    pagina = (SITE_TEMPLATE
              .replace("__TITULO__", html.escape(site.get("titulo", "Radar de artigos")))
              .replace("__SUBTITULO__", html.escape(site.get("subtitulo", "")))
              .replace("__ATUALIZADO__", hoje.strftime("%d/%m/%Y"))
              .replace("__SUPABASE__", supabase_json)
              .replace("__FILTROS__", filtros_json)
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
    h = json.dumps([cfg.get("filtro_revistas"), cfg.get("excluir"), c, cfg["topicos"],
                    cfg.get("filtros")], sort_keys=True, default=str)
    if state.get("classicos_hash") != h:
        state["fila_classicos"] = {}      # filtro mudou: refaz a lista
        state["classicos_hash"] = h
    fila = state.setdefault("fila_classicos", {})
    comp = compilar_facetas(cfg)
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
            for r in recs:
                r["facetas"] = classificar(r["titulo"], r.get("resumo"), comp)
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
    comp = compilar_facetas(cfg)
    fh = hash_filtros(cfg)
    if state.get("facetas_hash") != fh:
        for d in state.get("arquivo", []):
            d["facetas"] = classificar(d.get("titulo"), d.get("resumo"), comp)
        state["facetas_hash"] = fh
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
    novas_chaves = set()

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
            novas_chaves.add(r["key"])
            novas_chaves.add("t:" + norm_title(r["titulo"]))
            r["facetas"] = classificar(r["titulo"], r.get("resumo"), comp)
            reg = para_site(r, t["nome"], "novo", hoje.isoformat())
            arquivo.append(reg)
            todos_novos.append(reg)
        log(f"{t['nome']}: {len(novos)} novos")

    vistos |= novas_chaves
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
