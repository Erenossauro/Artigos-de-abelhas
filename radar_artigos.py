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
import math
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
    ultimo = "sem resposta"
    for i in range(tries):
        try:
            r = requests.get(url, params=params, headers=headers, timeout=45)
            if r.status_code in (401, 403):
                raise RuntimeError(f"acesso negado (código {r.status_code}): confira a chave OPENALEX_API_KEY")
            if r.status_code == 429:
                ultimo = "429: limite diário de uso (ou de velocidade) atingido"
                time.sleep(3 * (i + 1))
                continue
            if r.status_code >= 500:
                ultimo = f"erro do servidor ({r.status_code})"
                time.sleep(3 * (i + 1))
                continue
            r.raise_for_status()
            return r.json()
        except requests.RequestException as e:
            ultimo = str(e)
            if i < tries - 1:
                time.sleep(3 * (i + 1))
    raise RuntimeError(f"falhou depois de {tries} tentativas — {ultimo}")


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


def definicao_filtros_js(cfg):
    """Categorias com as palavras de cada opção (o site classifica artigos buscados ao vivo)."""
    out = []
    for f in cfg.get("filtros") or []:
        out.append({"nome": f["nome"], "rotulo_sem": f.get("rotulo_sem", "Não identificado"),
                    "opcoes": [{"nome": o["nome"], "termos": [str(t) for t in (o.get("termos") or [])],
                                "termos_titulo": [str(t) for t in (o.get("termos_titulo") or [])]}
                               for o in f.get("opcoes") or []]})
    return out


VOCABULARIO_PADRAO = [
    {"conceito": "Socialidade", "aliases": ["socialidade", "eussocialidade", "sociabilidade", "comportamento social", "vida social"],
     "palavras": ["eusociality", "eusocial", "social behavior", "division of labor", "caste", "queen", "worker", "kin selection", "colony organization", "altruism"]},
    {"conceito": "Termorregulação", "aliases": ["termorregulacao", "temperatura do ninho", "calor", "estresse termico", "tolerancia termica"],
     "palavras": ["thermoregulation", "heat stress", "thermal tolerance", "nest temperature", "brood temperature", "fanning", "heat wave", "critical thermal maximum", "cooling"]},
    {"conceito": "Mudanças climáticas", "aliases": ["mudancas climaticas", "clima", "aquecimento global", "seca", "fenologia"],
     "palavras": ["climate change", "global warming", "drought", "extreme weather", "phenology", "range shift", "species distribution model", "warming"]},
    {"conceito": "Ecologia urbana", "aliases": ["ecologia urbana", "urbanizacao", "cidade", "cidades", "areas verdes", "urbano"],
     "palavras": ["urban ecology", "urbanization", "city", "green space", "urban garden", "heat island", "impervious surface", "urban bee"]},
    {"conceito": "Nidificação e ninhos-isca", "aliases": ["ninho", "ninhos", "ninhos-isca", "ninho-isca", "nidificacao", "arquitetura do ninho"],
     "palavras": ["trap nest", "trap-nesting", "cavity-nesting", "nest box", "bee hotel", "nesting biology", "nest architecture", "nest site", "nest entrance", "ground-nesting"]},
    {"conceito": "Forrageamento", "aliases": ["forrageamento", "forragear", "coleta de nectar", "coleta de polen", "voo de forrageio"],
     "palavras": ["foraging", "foraging range", "flight distance", "foraging behavior", "pollen collection", "nectar collection", "optimal foraging", "resource use", "recruitment"]},
    {"conceito": "Comunicação", "aliases": ["comunicacao", "feromonio", "feromonios", "danca", "recrutamento"],
     "palavras": ["communication", "pheromone", "chemical communication", "cuticular hydrocarbons", "recruitment", "waggle dance", "vibrational signal", "olfactory communication"]},
    {"conceito": "Cognição e aprendizado", "aliases": ["cognicao", "aprendizado", "aprendizagem", "memoria", "navegacao", "orientacao"],
     "palavras": ["learning", "memory", "cognition", "olfactory learning", "visual learning", "navigation", "decision making", "behavioral variation"]},
    {"conceito": "Defesa e agressividade", "aliases": ["defesa", "defesa do ninho", "agressividade", "agressao", "guarda", "saque"],
     "palavras": ["nest defense", "guard bees", "aggression", "defensive behavior", "robbing", "cleptobiosis", "alarm pheromone"]},
    {"conceito": "Polinização", "aliases": ["polinizacao", "polinizador", "polinizadores", "visitantes florais", "rede de polinizacao"],
     "palavras": ["pollination", "pollinator", "pollination service", "crop pollination", "pollen transfer", "flower visitation", "pollination network", "buzz pollination"]},
    {"conceito": "Recursos florais e pólen", "aliases": ["recursos florais", "polen", "nectar", "flores", "plantas nativas", "palinologia"],
     "palavras": ["floral resources", "pollen", "nectar", "floral preference", "pollen analysis", "palynology", "host plant", "pollen diet", "plant-pollinator interaction", "oligolectic"]},
    {"conceito": "Conservação", "aliases": ["conservacao", "declinio", "extincao", "ameaca", "ameacadas", "restauracao"],
     "palavras": ["conservation", "extinction risk", "pollinator decline", "habitat loss", "restoration", "endangered", "threatened species", "red list"]},
    {"conceito": "Biodiversidade", "aliases": ["biodiversidade", "diversidade", "riqueza de especies", "composicao de especies", "inventario", "lista de especies"],
     "palavras": ["biodiversity", "species richness", "species diversity", "community composition", "functional diversity", "beta diversity", "species checklist", "inventory"]},
    {"conceito": "Amostragem e métodos", "aliases": ["amostragem", "metodo de coleta", "armadilha", "monitoramento", "transecto"],
     "palavras": ["sampling", "pan trap", "bee bowl", "netting", "transect", "monitoring protocol", "sampling effort", "standardized sampling"]},
    {"conceito": "Pesticidas", "aliases": ["agrotoxicos", "agrotoxico", "pesticidas", "inseticida", "neonicotinoide", "toxicidade", "defensivos"],
     "palavras": ["pesticide", "neonicotinoid", "insecticide", "glyphosate", "sublethal effects", "toxicity", "agrochemical", "fungicide", "exposure"]},
    {"conceito": "Doenças e parasitas", "aliases": ["doencas", "doenca", "parasitas", "patogenos", "virus", "varroa", "nosema"],
     "palavras": ["disease", "pathogen", "parasite", "Varroa", "Nosema", "virus", "deformed wing virus", "foulbrood", "immune response"]},
    {"conceito": "Nutrição", "aliases": ["nutricao", "alimentacao", "dieta", "proteina", "inanicao"],
     "palavras": ["nutrition", "diet", "protein", "lipid", "amino acids", "pollen quality", "starvation", "nutritional ecology", "feeding"]},
    {"conceito": "Mel e própolis", "aliases": ["mel", "propolis", "geopropolis", "mel de pote", "polen armazenado"],
     "palavras": ["honey", "pot-honey", "propolis", "geopropolis", "bee bread", "pot-pollen", "honey composition", "antimicrobial"]},
    {"conceito": "Microbioma e fermentação", "aliases": ["microbioma", "microbiota", "fermentacao", "bacterias", "leveduras", "simbiontes"],
     "palavras": ["microbiome", "microbiota", "gut bacteria", "yeast", "fermentation", "symbiont", "lactic acid bacteria"]},
    {"conceito": "Genética e genômica", "aliases": ["genetica", "genomica", "genoma", "transcriptoma", "expressao genica", "dna"],
     "palavras": ["genome", "genomic", "population genetics", "microsatellite", "transcriptome", "RNA-seq", "DNA barcoding", "gene expression", "epigenetic"]},
    {"conceito": "Filogenia e taxonomia", "aliases": ["filogenia", "taxonomia", "sistematica", "especie nova", "biogeografia"],
     "palavras": ["phylogeny", "taxonomy", "systematics", "new species", "species delimitation", "biogeography", "molecular phylogeny", "revision"]},
    {"conceito": "Reprodução (rainha e machos)", "aliases": ["reproducao", "rainha", "rainhas", "zangao", "zangoes", "machos", "acasalamento", "determinacao do sexo"],
     "palavras": ["queen", "drone", "mating", "reproduction", "oviposition", "sex determination", "worker reproduction", "queen rearing", "polyandry"]},
    {"conceito": "Enxameação e fundação", "aliases": ["enxameacao", "enxame", "fundacao de colonia", "divisao de colonia", "abandono"],
     "palavras": ["swarming", "colony founding", "reproductive swarming", "colony fission", "nest relocation", "absconding"]},
    {"conceito": "Ciclo de vida e diapausa", "aliases": ["diapausa", "ciclo de vida", "sazonalidade", "hibernacao", "emergencia"],
     "palavras": ["diapause", "phenology", "seasonal activity", "overwintering", "life cycle", "emergence"]},
    {"conceito": "Morfologia e características funcionais", "aliases": ["morfologia", "tamanho do corpo", "lingua", "caracteres funcionais", "voo"],
     "palavras": ["functional traits", "body size", "intertegular distance", "tongue length", "morphology", "flight performance", "wing"]},
    {"conceito": "Monitoramento eletrônico", "aliases": ["sensores", "sensor", "monitoramento eletronico", "iot", "apicultura de precisao", "inteligencia artificial"],
     "palavras": ["sensor", "Internet of Things", "precision beekeeping", "hive monitoring", "machine learning", "computer vision", "acoustic monitoring", "RFID", "bee counting"]},
    {"conceito": "Meliponicultura e manejo", "aliases": ["meliponicultura", "manejo", "criacao de abelhas", "caixas", "divisao de caixas"],
     "palavras": ["meliponiculture", "stingless beekeeping", "colony management", "rearing", "artificial diet", "colony division", "hive design", "management"]},
    {"conceito": "Paisagem e uso da terra", "aliases": ["paisagem", "uso da terra", "fragmentacao", "conectividade", "cobertura florestal", "agricultura"],
     "palavras": ["landscape", "land use", "habitat fragmentation", "agricultural landscape", "forest cover", "connectivity", "landscape ecology"]},
    {"conceito": "Espécies invasoras e competição", "aliases": ["invasoras", "exoticas", "competicao", "sobreposicao de nicho"],
     "palavras": ["invasive species", "exotic species", "alien species", "competition", "niche overlap", "resource competition"]},
    {"conceito": "Abelhas solitárias", "aliases": ["abelhas solitarias", "solitarias", "abelha solitaria"],
     "palavras": ["solitary bee", "mason bee", "leafcutter bee", "Osmia", "Megachile", "Xylocopa", "Andrena", "cavity-nesting"]},
    {"conceito": "Abelhas sem ferrão", "aliases": ["sem ferrao", "meliponini", "meliponineos", "jatai", "mandacaia", "uruçu", "urucu"],
     "palavras": ["stingless bee", "Meliponini", "Melipona", "Trigona", "Tetragonula", "Scaptotrigona", "Tetragonisca", "meliponine"]},
    {"conceito": "Mamangavas", "aliases": ["mamangavas", "mamangava", "bombus", "abelhas de cauda"],
     "palavras": ["bumble bee", "bumblebee", "Bombus", "bumble bee decline", "colony growth", "queen bumble bee"]},
    {"conceito": "Abelhas das orquídeas", "aliases": ["orquideas", "euglossini", "abelhas das orquideas", "fragrancias"],
     "palavras": ["orchid bee", "Euglossini", "Euglossa", "Eulaema", "fragrance collection", "male perfume"]},
    {"conceito": "Fisiologia", "aliases": ["fisiologia", "metabolismo", "respiracao", "balanco hidrico", "estresse oxidativo", "energetica"],
     "palavras": ["metabolism", "respiration", "energetics", "water balance", "desiccation", "thermal physiology", "oxidative stress"]},
    {"conceito": "Sobrevivência e longevidade", "aliases": ["sobrevivencia", "longevidade", "mortalidade", "envelhecimento"],
     "palavras": ["survival", "longevity", "mortality", "lifespan", "senescence"]},
    {"conceito": "Redes de interação", "aliases": ["redes de interacao", "aninhamento", "especializacao", "generalizacao", "redes ecologicas"],
     "palavras": ["interaction network", "nestedness", "network structure", "specialization", "generalization", "plant-pollinator network"]},
    {"conceito": "Cleptoparasitismo", "aliases": ["cleptoparasitismo", "parasitismo social", "cleptoparasita", "lestrimelitta"],
     "palavras": ["cleptoparasitism", "social parasitism", "brood parasite", "Lestrimelitta", "cuckoo bee"]},
]


REVISTAS_SUGERIDAS = [
    {"nome": "Apidologie", "issns": ["0044-8435", "1297-9678"]},
    {"nome": "Journal of Apicultural Research", "issns": ["0021-8839", "2078-6913"]},
    {"nome": "Bee World", "issns": ["0005-772X"]},
]


def padrao_para_site(cfg, state):
    """Sugestões que aparecem na janela de configuração da primeira visita."""
    topicos = [{"nome": t["nome"], "termos": [str(x) for x in t["contexto"]]}
               for t in cfg.get("topicos") or [] if t.get("contexto")]
    cache = (state or {}).get("fontes") or {}
    revistas, vistos = [], set()
    for e in _entradas_revistas(cfg, "revistas_de_abelhas"):
        nome = e["nome"]
        curada = next((c for c in REVISTAS_SUGERIDAS
                       if _eh_issn_str(nome) and _issn_norm(nome) in {_issn_norm(i) for i in c["issns"]}), None)
        info = cache.get(norm_j(nome))
        if curada:
            item = {"nome": curada["nome"], "issns": list(curada["issns"])}
        elif info:
            item = {"nome": info.get("nome") or nome, "issns": [info["issn"]] if info.get("issn") else []}
        elif _eh_issn_str(nome):
            item = {"nome": nome, "issns": [nome if "-" in nome else nome[:4] + "-" + nome[4:]]}
        else:
            item = {"nome": nome, "issns": []}
        item["padrao"] = True
        if norm_j(item["nome"]) not in vistos:
            vistos.add(norm_j(item["nome"]))
            revistas.append(item)
    for c in REVISTAS_SUGERIDAS:
        if norm_j(c["nome"]) not in vistos:
            revistas.append(dict(c, padrao=False))
    vocab = list(VOCABULARIO_PADRAO)
    for v in cfg.get("vocabulario") or []:   # o config.yaml pode acrescentar conceitos
        if isinstance(v, dict) and v.get("conceito") and v.get("palavras"):
            vocab.append({"conceito": str(v["conceito"]), "aliases": [str(a) for a in v.get("aliases") or []],
                          "palavras": [str(p) for p in v["palavras"]]})
    return {"topicos": topicos, "revistas": revistas, "vocabulario": vocab,
            "termos_abelha": termos_abelha(cfg), "rigor": str((cfg.get("abelhas") or {}).get("rigor", "normal")),
            "colecao": str((cfg.get("zotero") or {}).get("colecao") or "Radar de Abelhas")}


def _eh_issn_str(x):
    return bool(re.fullmatch(r"\d{4}-?\d{3}[\dXx]", str(x).strip()))


# ----------------------------------------------------------------------------
# Abelha do dia (foto do iNaturalist)
# ----------------------------------------------------------------------------
INAT_TAXA = "https://api.inaturalist.org/v1/taxa"
ESPECIES_FOTO_PADRAO = [
    "Melipona quadrifasciata", "Bombus terrestris", "Apis cerana", "Tetragonisca angustula", "Xylocopa frontalis",
    "Osmia bicornis", "Euglossa cordata", "Bombus pauloensis", "Scaptotrigona postica", "Centris analis",
    "Apis mellifera", "Andrena flavipes", "Trigona spinipes", "Megachile rotundata", "Melipona scutellaris",
    "Bombus impatiens", "Eulaema nigrita", "Halictus rubicundus", "Plebeia droryana", "Xylocopa virginica",
    "Frieseomelitta varia", "Lasioglossum zephyrum", "Bombus lapidarius", "Melipona subnitida", "Agapostemon virescens",
    "Partamona helleri", "Osmia lignaria", "Apis dorsata", "Nannotrigona testaceicornis", "Ceratina calcarata",
    "Bombus morio", "Augochlora pura", "Tetragonula carbonaria", "Anthophora plumipes", "Oxytrigona tataira",
    "Bombus vosnesenskii", "Melipona beecheii", "Colletes hederae", "Xylocopa violacea", "Exaerete smaragdina",
    "Lestrimelitta limao", "Habropoda laboriosa", "Bombus pascuorum", "Trigona fulviventris", "Meliponula bocandei",
]


def _foto_livre(f):
    lic = str((f or {}).get("license_code") or "").strip().lower()
    return bool(lic) and "reserved" not in lic and lic not in ("none", "null")


def _fotos_de_especie(nome, maximo=1):
    """Até 'maximo' fotos livres (Creative Commons) da espécie. Devolve (lista de fotos, nome encontrado no iNaturalist)."""
    res = (get_json(INAT_TAXA, {"q": nome, "per_page": 5}).get("results") or [])
    if not res:
        return [], None
    alvo = norm_j(nome)
    tx = next((x for x in res if norm_j(x.get("name")) == alvo), res[0])
    candidatas = []
    dp = tx.get("default_photo") or {}
    if _foto_livre(dp):
        candidatas.append(dp)
    if len(candidatas) < maximo:   # procura mais fotos livres da mesma espécie
        det = (get_json(f"{INAT_TAXA}/{tx['id']}", {}).get("results") or [{}])[0]
        for tp in det.get("taxon_photos") or []:
            f = tp.get("photo") or {}
            if _foto_livre(f) and all(f.get("id") is None or f.get("id") != c.get("id") for c in candidatas):
                candidatas.append(f)
            if len(candidatas) >= maximo:
                break
    fotos = []
    for f in candidatas[:maximo]:
        url = f.get("large_url") or (f.get("url") or "").replace("square", "large") or f.get("medium_url") or ""
        if url:
            fotos.append({"nome_cientifico": tx.get("name") or nome, "nome_popular": tx.get("preferred_common_name") or "",
                          "url": url, "credito": f.get("attribution") or "", "licenca": str(f.get("license_code") or "").upper(),
                          "link": f"https://www.inaturalist.org/taxa/{tx['id']}"})
    return fotos, tx.get("name")


def _foto_de_especie(nome):
    fotos, _ = _fotos_de_especie(nome, 1)
    return fotos[0] if fotos else None


def altura_foto(cfg):
    """Altura máxima da foto do topo, em pixels (config: foto_do_dia > altura)."""
    try:
        return max(200, min(900, int((cfg.get("foto_do_dia") or {}).get("altura", 420))))
    except (TypeError, ValueError):
        return 420


def modo_foto(cfg):
    m = str((cfg.get("foto_do_dia") or {}).get("modo", "aleatoria")).strip().lower()
    return "dia" if m in ("dia", "do_dia", "diaria") else "aleatoria"


def fotos_das_especies(cfg, state, hoje):
    """Busca (e guarda em cache) fotos livres de TODAS as espécies escritas no config. O site sorteia uma a cada visita."""
    c = cfg.get("foto_do_dia") or {}
    if c.get("ativo") is False:
        return []
    especies = []
    for x in (c.get("especies") or ESPECIES_FOTO_PADRAO):
        x = str(x).strip()
        if x and norm_j(x) not in {norm_j(e) for e in especies}:
            especies.append(x)
    try:
        por = max(1, min(5, int(c.get("fotos_por_especie", 1) or 1)))
    except (TypeError, ValueError):
        por = 1
    cache = state.setdefault("fotos_cache", {})
    chaves = {norm_j(e) for e in especies}
    for k in [k for k in cache if k not in chaves]:   # espécies que saíram da lista
        del cache[k]
    todas, sem = [], []
    for nome in especies:
        chave = norm_j(nome)
        reg = cache.get(chave)
        try:
            idade = (hoje - date.fromisoformat(reg["data"])).days if reg else 999
            velho = (not reg) or reg.get("por") != por or idade > (45 if reg.get("fotos") else 7)   # sem foto: tenta de novo em 7 dias
        except (ValueError, KeyError, TypeError):
            velho = True
        if velho:
            try:
                fotos, achado = _fotos_de_especie(nome, por)
                reg = {"data": hoje.isoformat(), "por": por, "fotos": fotos, "nome": achado}
                cache[chave] = reg
                time.sleep(0.4)   # educação com o iNaturalist
            except Exception as e:
                log(f"⚠ Foto ({nome}): {e}")
        if reg and reg.get("fotos"):
            todas.extend(reg["fotos"])
            if reg.get("nome") and norm_j(reg["nome"]) != chave:
                log(f"ℹ \"{nome}\" foi encontrado no iNaturalist como \"{reg['nome']}\"")
        else:
            sem.append(nome)
    if sem:
        log("⚠ Sem foto livre no iNaturalist para: " + ", ".join(sem) + " (confira se o nome científico está certo)")
    log(f"Fotos: {len(todas)} foto(s) de {len(especies) - len(sem)} das {len(especies)} espécies")
    return todas


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
# Lista de revistas da Scopus (Source List) — filtro opcional
# ----------------------------------------------------------------------------
_CACHE_SCOPUS = {}


def _linhas_tabela(caminho):
    """Lê .csv (separador ; ou ,) ou .xlsx e devolve (cabecalho, linhas)."""
    if caminho.suffix.lower() in (".xlsx", ".xlsm"):
        import openpyxl  # só é necessário para arquivos .xlsx

        wb = openpyxl.load_workbook(caminho, read_only=True, data_only=True)
        for ws in wb.worksheets:
            it = ws.iter_rows(values_only=True)
            cab = next(it, None)
            nomes = [str(c or "").strip().lower() for c in (cab or [])]
            if "source title" in nomes and ("issn" in nomes or "print-issn" in nomes):
                return nomes, ([("" if c is None else str(c)).strip() for c in lin] for lin in it)
        raise ValueError("nenhuma aba com as colunas 'Source Title' e 'ISSN'")
    texto = caminho.read_text(encoding="utf-8-sig", errors="replace")
    primeira = texto.split("\n", 1)[0]
    delim = ";" if primeira.count(";") >= primeira.count(",") else ","
    leitor = csv.reader(io.StringIO(texto), delimiter=delim)
    cab = [h.strip().lower() for h in next(leitor, [])]
    return cab, leitor


def carregar_scopus(cfg):
    """Devolve {'issn': set, 'titulos': set, ...} ou None se o filtro estiver desligado/sem arquivo."""
    sc = cfg.get("scopus") or {}
    if not sc.get("ativo"):
        return None
    caminho = ROOT / sc.get("arquivo", "scopus.csv")
    if not caminho.exists():
        log(f"⚠ O filtro da Scopus está ligado, mas o arquivo {caminho.name} não foi encontrado. Filtro IGNORADO.")
        return None
    somente_ativas = bool(sc.get("somente_ativas", True))
    tipos = tuple(str(t).strip().lower() for t in (sc.get("tipos") or []))
    st = caminho.stat()
    chave = (str(caminho), st.st_mtime, st.st_size, somente_ativas, tipos)
    if chave in _CACHE_SCOPUS:
        return _CACHE_SCOPUS[chave]
    try:
        cab, linhas = _linhas_tabela(caminho)

        def col(*nomes):
            for n in nomes:
                if n in cab:
                    return cab.index(n)
            return None

        i_tit = col("source title", "title")
        i_issn = col("issn", "print-issn", "print issn")
        i_eissn = col("eissn", "e-issn", "e issn")
        i_st = col("active or inactive", "status")
        i_tp = col("source type", "type")
        if i_tit is None or (i_issn is None and i_eissn is None):
            raise ValueError("faltam as colunas Source Title / ISSN")
        issns, titulos, total = set(), set(), 0
        for lin in linhas:
            def v(i):
                return lin[i].strip() if i is not None and i < len(lin) and lin[i] is not None else ""
            if somente_ativas and i_st is not None and v(i_st).lower() != "active":
                continue
            if tipos and i_tp is not None and v(i_tp).lower() not in tipos:
                continue
            total += 1
            for i in (i_issn, i_eissn):
                k = _issn_norm(v(i))
                if len(k) == 8:
                    issns.add(k)
            if v(i_tit):
                titulos.add(norm_j(v(i_tit)))
        if total == 0:
            raise ValueError("nenhuma revista passou nas regras (status/tipo)")
        res = {"issn": issns, "titulos": titulos, "n": total, "assinatura": (st.st_mtime, st.st_size)}
        log(f"Scopus: {total} revistas na lista ({len(issns)} ISSNs)")
        _CACHE_SCOPUS[chave] = res
        return res
    except Exception as e:
        log(f"⚠ Não consegui usar a lista da Scopus ({e}). Filtro IGNORADO.")
        return None


def scopus_ok(r, escopo):
    if escopo is None:
        return True
    for i in r.get("issn") or []:
        if _issn_norm(i) in escopo["issn"]:
            return True
    return norm_j(r.get("revista")) in escopo["titulos"] if r.get("revista") else False


# ----------------------------------------------------------------------------
# Modo amplo: busca tudo que cita abelhas; os temas viram etiquetas/filtros no site
# ----------------------------------------------------------------------------
# O que conta como "citar abelhas". Além de "bee", nomes de grupos: muitos artigos só dizem "Apis cerana",
# "Bombus terrestris" ou "Osmia bicornis" e nunca a palavra "bee" (frases com "Apis" para não confundir com "APIs" de programação).
TERMOS_ABELHA_PADRAO = [
    "bee", "honeybee", "honey bee", "bumblebee", "bumble bee", "Anthophila", "Apoidea", "Apidae", "Meliponini",
    "Apis cerana", "Apis mellifera", "Apis dorsata", "Apis florea",
    "Bombus", "Melipona", "Trigona", "Tetragonula", "Scaptotrigona", "Euglossa", "Eulaema",
    "Osmia", "Megachile", "Xylocopa", "Andrena", "Lasioglossum", "Halictus", "Ceratina", "Centris", "Colletes",
]


def modo_busca(cfg):
    m = str((cfg.get("busca") or {}).get("modo", "amplo")).strip().lower()
    if m in ("revistas", "revista"):
        return "revistas"
    return "por_tema" if m in ("por_tema", "tema", "temas") else "amplo"


def termos_abelha(cfg):
    return list((cfg.get("abelhas") or {}).get("termos") or TERMOS_ABELHA_PADRAO)


def compilar_temas(cfg):
    """Cada tópico com 'contexto' vira uma etiqueta de tema; o sem 'contexto' é o 'resto'."""
    base = {str(t).lower() for t in termos_abelha(cfg)}
    comp, sem = [], "Outros temas de abelhas"
    for t in cfg.get("topicos") or []:
        ctx = [_padrao(x) for x in (t.get("contexto") or []) if str(x).strip()]
        if not ctx:
            sem = t["nome"]
            continue
        termos = {str(x).lower() for x in t.get("termos") or []}
        p_termos = None if termos == base else [_padrao(x) for x in termos]   # tópicos específicos exigem seus termos
        comp.append((t["nome"], p_termos, ctx))
    return comp, sem


def classificar_temas(r, comp_sem):
    comp, sem = comp_sem
    texto = ((r.get("titulo") or "") + " " + (r.get("resumo") or "") + " " +
             " ".join(r.get("palavras") or [])).lower()
    temas = [nome for nome, p_termos, ctx in comp
             if (p_termos is None or any(p.search(texto) for p in p_termos))
             and any(p.search(texto) for p in ctx)]
    return temas or [sem]


def hash_temas(cfg):
    return json.dumps([(t.get("nome"), t.get("termos"), t.get("contexto")) for t in cfg.get("topicos") or []]
                      + [termos_abelha(cfg)], sort_keys=True, default=str, ensure_ascii=False)


# ----------------------------------------------------------------------------
# Modo "revistas": você escreve as revistas e entra TUDO o que elas publicam
# ----------------------------------------------------------------------------
def _entradas_revistas(cfg, chave="revistas"):
    out = []
    for e in cfg.get(chave) or []:
        if isinstance(e, dict):
            nome, so = str(e.get("nome") or e.get("issn") or "").strip(), bool(e.get("so_abelhas"))
        else:
            nome, so = str(e).strip(), False
        if nome:
            out.append({"nome": nome, "so_abelhas": so})
    return out


def _auth_openalex():
    p = {}
    if os.getenv("OPENALEX_MAILTO"):
        p["mailto"] = os.environ["OPENALEX_MAILTO"]
    if os.getenv("OPENALEX_API_KEY"):
        p["api_key"] = os.environ["OPENALEX_API_KEY"]
    return p


def resolver_fonte(nome, cache):
    """Acha a revista no OpenAlex (por nome ou ISSN). Guarda no cache para não repetir a consulta."""
    chave = norm_j(nome) or nome.lower()
    if chave in cache:
        return cache[chave]
    info = None
    if re.fullmatch(r"\d{4}-?\d{3}[\dXx]", nome.strip()):
        issn = nome.strip() if "-" in nome else nome.strip()[:4] + "-" + nome.strip()[4:]
        dados = get_json(f"{OPENALEX_FONTES}/issn:{issn}", _auth_openalex())
        contar_custo(dados)
        if dados.get("id"):
            info = {"id": dados["id"].rsplit("/", 1)[-1], "nome": dados.get("display_name") or issn,
                    "issn": dados.get("issn_l") or issn, "exato": True}
    else:
        dados = get_json(OPENALEX_FONTES, dict(_auth_openalex(), search=nome, **{"per-page": 5}))
        contar_custo(dados)
        res = dados.get("results", [])
        if res:
            esc = next((x for x in res if norm_j(x.get("display_name")) == norm_j(nome)), None)
            info = {"id": (esc or res[0])["id"].rsplit("/", 1)[-1], "nome": (esc or res[0]).get("display_name"),
                    "issn": (esc or res[0]).get("issn_l") or "", "exato": esc is not None}
    if info:
        cache[chave] = info
    return info


def resolver_todas(cfg, state, chave="revistas"):
    """[(entrada, info)] de todas as revistas do config; avisa as que não achou ou que ficaram duvidosas."""
    cache = state.setdefault("fontes", {})
    out = []
    for e in _entradas_revistas(cfg, chave):
        try:
            info = resolver_fonte(e["nome"], cache)
        except Exception as ex:
            log(f"⚠ Não consegui consultar a revista \"{e['nome']}\": {ex}")
            continue
        if not info:
            log(f"⚠ Não encontrei a revista \"{e['nome']}\" no OpenAlex. Tente escrever o ISSN.")
            continue
        aviso = "" if info["exato"] else "   ⚠ o nome não é idêntico: confira ou use o ISSN"
        log(f"Revista \"{e['nome']}\" → {info['nome']} ({info['issn'] or 'sem ISSN'}){aviso}")
        out.append((e, info))
    return out


def coletar_revistas(cfg, state, ini, fim, b, chave="revistas"):
    """Tudo que as revistas escolhidas publicaram na janela (com 'so_abelhas', só o que cita abelhas).
    Os artigos de revistas "inteiras" saem marcados com completa=True: nenhum filtro os barra."""
    resolvidas = resolver_todas(cfg, state, chave)
    ids_tudo = [i["id"] for e, i in resolvidas if not e["so_abelhas"]]
    ids_abelha = [i["id"] for e, i in resolvidas if e["so_abelhas"]]
    recs, erros = [], 0
    for ids, so_abelhas in ((ids_tudo, False), (ids_abelha, True)):
        for k in range(0, len(ids), 50):
            filtros = ["primary_location.source.id:" + "|".join(ids[k:k + 50]),
                       "type:" + "|".join(TIPOS_ACEITOS),
                       f"from_publication_date:{ini}", f"to_publication_date:{fim}"]
            if so_abelhas:
                filtros.append("title_and_abstract.search:" + topic_query({"termos": termos_abelha(cfg)}))
            try:
                params = _params_openalex(filtros, "publication_date:desc", 100)
                lote = [_rec_openalex(w) for w in _paginar_openalex(params, int(b.get("max_paginas", 100)), 100)]
                if not so_abelhas:
                    for r in lote:
                        r["completa"] = True
                recs += lote
            except Exception as ex:
                erros += 1
                log(f"Erro ao buscar as revistas: {ex}")
    return recs, erros


# ----------------------------------------------------------------------------
# Por que o artigo entrou? (motivo gravado em cada artigo) e rigor da busca
# ----------------------------------------------------------------------------
def motivo_de(r, cfg, escopo=None):
    """Registra como o artigo chegou ao radar: o site mostra isso em "Por que entrou?"."""
    if r.get("completa"):
        return {"via": "revista", "revista": r.get("revista") or ""}
    textos = (("título", (r.get("titulo") or "").lower()), ("resumo", (r.get("resumo") or "").lower()),
              ("palavras-chave", " ".join(r.get("palavras") or []).lower()))
    achou = []
    for x in termos_abelha(cfg):
        p = _padrao(x)
        onde = [nome for nome, txt in textos if txt and p.search(txt)]
        if onde:
            achou.append([x, "+".join(onde)])
    return {"via": "busca", "achou": achou[:10], "fonte": r.get("fonte") or ""}


def passa_rigor(m, rigor):
    """normal: qualquer termo | medio: termo no título/palavras-chave OU 2 termos diferentes | alto: termo no título/palavras-chave."""
    rigor = str(rigor or "normal").strip().lower()
    if m.get("via") != "busca" or rigor == "normal":
        return True
    achou = m.get("achou") or []
    forte = any("título" in lugar or "palavras-chave" in lugar for _, lugar in achou)
    if rigor == "alto":
        return forte
    return forte or len(achou) >= 2


def motivo_classico(r, t):
    txt = ((r.get("titulo") or "") + " " + (r.get("resumo") or "")).lower()
    achou = lambda lst: [x for x in (lst or []) if _padrao(x).search(txt)][:6]
    return {"via": "classico", "tema": t["nome"], "termos": achou(t.get("termos")), "contexto": achou(t.get("contexto")),
            "citacoes": r.get("citacoes") or 0}


# ----------------------------------------------------------------------------
# Janela das Novidades (só os últimos N dias)
# ----------------------------------------------------------------------------
def novidades_dias(cfg):
    v = (cfg.get("site") or {}).get("novidades_dias", 7)
    try:
        return int(v) if v else 0
    except (TypeError, ValueError):
        return 7


def historico_dias(cfg):
    """Quantos dias de histórico o site guarda (0 = sem limite). Nunca menor que a janela padrão."""
    site = cfg.get("site") or {}
    try:
        v = int(site.get("historico_dias", 90) or 0)
    except (TypeError, ValueError):
        v = 90
    return max(v, novidades_dias(cfg)) if v else 0


def janelas_site(cfg):
    """Passos do controle deslizante, em dias; 0 = todo o histórico."""
    hist = historico_dias(cfg)
    padrao = novidades_dias(cfg)
    base = (cfg.get("site") or {}).get("janelas") or [3, 7, 15, 30, 60, 90, 180, 365]
    passos = {int(x) for x in base if int(x) > 0 and (not hist or int(x) <= hist)}
    if padrao:
        passos.add(padrao)
    return sorted(passos) + [0]


def na_janela(d, hoje, dias):
    """True se a data de publicação do artigo está dentro dos últimos 'dias'."""
    if not dias:
        return True
    ref = (d.get("data") or d.get("adicionado") or "")[:10]
    if d.get("tardio") and d.get("adicionado"):   # o OpenAlex cadastrou depois: vale a data em que chegou ao radar
        ref = max(ref, d["adicionado"][:10])
    try:
        return date.fromisoformat(ref) >= hoje - timedelta(days=dias)
    except ValueError:
        return True


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


TIPOS_ACEITOS = ("article", "review", "preprint")


CUSTO = {"usd": 0.0, "chamadas": 0}


def contar_custo(data):
    CUSTO["chamadas"] += 1
    try:
        CUSTO["usd"] += float((data.get("meta") or {}).get("cost_usd") or 0)
    except (TypeError, ValueError):
        pass


def aviso_chave():
    if not os.getenv("OPENALEX_API_KEY"):
        log("⚠ OPENALEX_API_KEY não definida: o OpenAlex dá só US$ 0,10/dia sem chave "
            "(com uma chave grátis são US$ 1,00/dia). Veja o guia para criar a chave.")


def resumo_custo():
    chave = bool(os.getenv("OPENALEX_API_KEY"))
    log(f"OpenAlex: {CUSTO['chamadas']} chamadas, custo ≈ US$ {CUSTO['usd']:.4f} "
        f"(grátis até US$ {'1,00' if chave else '0,10'} por dia)")


def _rec_openalex(w):
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
        "tipo": w.get("type") or "",
        "palavras": [k.get("display_name") for k in (w.get("keywords") or []) if k.get("display_name")]
                    + [t.get("display_name") for t in (w.get("topics") or []) if t.get("display_name")],
        "oa": bool((w.get("open_access") or {}).get("is_oa")),
        "oa_url": (w.get("open_access") or {}).get("oa_url") or "",
        "criado": w.get("created_date") or "",
        "fonte_id": (src.get("id") or "").rsplit("/", 1)[-1],
    }
    rec["key"] = make_key(rec)
    return rec


def _params_openalex(filtros, sort, per_page):
    params = {"filter": ",".join(filtros), "sort": sort, "per-page": per_page}
    if os.getenv("OPENALEX_MAILTO"):
        params["mailto"] = os.environ["OPENALEX_MAILTO"]
    if os.getenv("OPENALEX_API_KEY"):
        params["api_key"] = os.environ["OPENALEX_API_KEY"]
    return params


def _paginar_openalex(params, paginas, per_page):
    resultados = []
    for pag in range(1, min(paginas or 100, 100) + 1):   # o OpenAlex só entrega até 10.000 resultados por busca
        params["page"] = pag
        data = get_json(OPENALEX_URL, params)
        contar_custo(data)
        lote = data.get("results", [])
        resultados += lote
        if len(lote) < per_page:
            break
    return resultados


def openalex_search(topico, ini=None, fim=None, sort="publication_date:desc",
                    per_page=100, ate_ano=None, paginas=1, extra_filtros=None):
    filtros = [f"title_and_abstract.search:{topic_query(topico)}",
               "type:" + "|".join(TIPOS_ACEITOS)]
    if ini:
        filtros.append(f"from_publication_date:{ini}")
    if fim:
        filtros.append(f"to_publication_date:{fim}")
    if ate_ano:
        filtros.append(f"to_publication_date:{ate_ano}-12-31")
    filtros += list(extra_filtros or [])
    params = _params_openalex(filtros, sort, per_page)
    return [_rec_openalex(w) for w in _paginar_openalex(params, paginas, per_page)]


def epmc_search(topico, ini, fim, page_size=100, kw=False):
    if kw:   # também procura nas palavras-chave dos autores (campo KW)
        partes = []
        for t in topico["termos"]:
            x = f'"{t}"' if (" " in t or "-" in t) else t
            partes += [f"TITLE_ABS:{x}", f"KW:{x}"]
        q = "(" + " OR ".join(partes) + ")"
    else:
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
            "palavras": [k for k in ((w.get("keywordList") or {}).get("keyword") or []) if isinstance(k, str)],
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
        "temas": r.get("temas") or [],
        "completa": bool(r.get("completa")),
        "tardio": bool(r.get("tardio")),
        "oa_url": r.get("oa_url") or "",
        "motivo": r.get("motivo"),
    }


SITE_TEMPLATE = r"""<!doctype html>
<html lang="pt-BR">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>__TITULO__</title>
<link rel="icon" href="data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 64 64'%3E%3Cpolygon points='32,3 58,18 58,46 32,61 6,46 6,18' fill='%2355663F'/%3E%3C/svg%3E">
<style>
  :root {
    --bg:#F3EEE4; --surface:#FBF8F3; --surface2:#EFE8DB; --ink:#2E2B25; --mut:#7A7364; --line:#DDD3C1;
    --verde:#55663F; --verde-esc:#3F4E2E; --verde-claro:#E4E8D6; --argila:#A15C38; --argila-claro:#F0DDD0;
    --ok:#4F7A3F; --err:#A5402F; --sombra:0 1px 2px rgba(60,48,30,.06), 0 6px 18px rgba(60,48,30,.06); --raio:14px;
    --serif:"Iowan Old Style","Palatino Linotype",Palatino,Georgia,"Times New Roman",serif;
    --sans:-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,"Helvetica Neue",Arial,sans-serif;
  }
  @media (prefers-color-scheme: dark) {
    :root { --bg:#1C1A16; --surface:#26231E; --surface2:#2F2B25; --ink:#ECE6D8; --mut:#A59E8C; --line:#3A362E;
      --verde:#9DB07F; --verde-esc:#2F3A22; --verde-claro:#333B27; --argila:#D4906A; --argila-claro:#3D2E24;
      --ok:#8DB87A; --err:#E08A78; --sombra:0 1px 2px rgba(0,0,0,.3), 0 6px 18px rgba(0,0,0,.25); }
  }
  * { box-sizing:border-box; }
  html { scroll-behavior:smooth; }
  body { margin:0; background:var(--bg); color:var(--ink); line-height:1.55; font-family:var(--sans); }
  a { color:inherit; }
  button { font-family:inherit; }

  /* ---------- topo com a foto do dia (a foto aparece INTEIRA, sem cortes) ---------- */
  .hero { position:relative; color:#fff; overflow:hidden; --foto-altura:__FOTO_ALTURA__px;
    background:linear-gradient(135deg,var(--verde-esc),#6d5a3c); }
  .hero-fundo { position:absolute; left:-40px; top:-40px; width:calc(100% + 80px); height:calc(100% + 80px); object-fit:cover; filter:blur(28px) brightness(.55) saturate(1.1); }
  .hero-sombra { position:absolute; inset:0; background:linear-gradient(180deg,rgba(20,16,10,.5) 0%,rgba(20,16,10,.12) 50%,rgba(20,16,10,.55) 100%); }
  .hero-in, .hero-corpo { position:relative; max-width:1180px; width:100%; margin:0 auto; padding-left:24px; padding-right:24px; }
  .hero-in { padding-top:22px; display:flex; justify-content:space-between; align-items:flex-start; gap:12px; }
  .hero-corpo { padding-top:20px; padding-bottom:26px; display:grid; grid-template-columns:minmax(0,1fr) auto; gap:28px; align-items:end; min-height:120px; }
  .hero.sem-foto .hero-corpo { min-height:70px; padding-top:6px; }
  .marca { display:flex; align-items:center; gap:14px; }
  .marca h1 { margin:0; font-family:var(--serif); font-size:30px; font-weight:600; letter-spacing:-.01em; text-shadow:0 1px 8px rgba(0,0,0,.35); }
  .marca .sub { font-size:13px; opacity:.9; margin-top:2px; text-shadow:0 1px 6px rgba(0,0,0,.4); }
  .hero-legenda { align-self:end; }
  .abelha-dia .rot { font-size:11px; letter-spacing:.12em; text-transform:uppercase; opacity:.85; }
  .abelha-dia .cient { font-family:var(--serif); font-size:28px; font-style:italic; text-shadow:0 1px 8px rgba(0,0,0,.5); line-height:1.2; }
  .abelha-dia .pop { font-size:15px; opacity:.92; margin-top:2px; }
  .credito { font-size:11px; opacity:.8; max-width:420px; margin-top:10px; }
  .credito a { text-decoration:underline; }
  .hero-foto { margin:0; position:relative; cursor:zoom-in; justify-self:end; }
  .hero-foto img { display:block; width:auto; height:auto; max-width:min(680px,62vw); max-height:var(--foto-altura); border-radius:14px; box-shadow:0 12px 36px rgba(0,0,0,.5); border:2px solid rgba(255,255,255,.2); }
  .hero-foto .ampliar { position:absolute; right:10px; bottom:10px; background:rgba(20,16,10,.62); color:#fff; font-size:12px; padding:4px 11px; border-radius:999px; pointer-events:none; }
  .btn-hero { border:1px solid rgba(255,255,255,.65); background:rgba(20,16,10,.28); color:#fff; padding:8px 16px; border-radius:999px; cursor:pointer; font-size:13px; font-weight:600; backdrop-filter:blur(4px); }
  .btn-hero:hover { background:rgba(255,255,255,.22); }
  .lightbox { position:fixed; inset:0; background:rgba(15,12,8,.93); display:none; align-items:center; justify-content:center; z-index:70; cursor:zoom-out; padding:18px; }
  .lightbox.on { display:flex; }
  .lightbox img { max-width:96vw; max-height:92vh; object-fit:contain; border-radius:8px; }

  /* ---------- layout ---------- */
  .layout { max-width:1180px; margin:26px auto 60px; padding:0 24px; display:grid; grid-template-columns:280px minmax(0,1fr); gap:30px; align-items:start; }
  .layout.leitura { grid-template-columns:minmax(0,1fr); }
  .layout.leitura .sidebar { display:none; }
  .sidebar { position:sticky; top:14px; max-height:calc(100vh - 28px); overflow:auto; padding-right:4px; }
  .sb-bloco { background:var(--surface); border:1px solid var(--line); border-radius:var(--raio); padding:14px 16px 10px; margin-bottom:14px; }
  .sb-titulo { font-size:12px; font-weight:700; letter-spacing:.08em; text-transform:uppercase; color:var(--verde); margin-bottom:8px; display:flex; justify-content:space-between; align-items:center; }
  .sb-titulo a { font-size:12px; text-transform:none; letter-spacing:0; font-weight:600; color:var(--argila); cursor:pointer; text-decoration:none; }
  .sb-bloco input[type=search] { width:100%; padding:8px 12px; font-size:13px; border:1px solid var(--line); border-radius:999px; background:var(--bg); color:var(--ink); margin-bottom:6px; }
  .sb-bloco select { width:100%; padding:9px 12px; font-size:14px; border:1px solid var(--line); border-radius:10px; background:var(--bg); color:var(--ink); margin-bottom:8px; }
  .lista-op { max-height:250px; overflow:auto; margin:0 -4px; padding:0 4px; }
  label.op { display:flex; align-items:center; gap:9px; padding:6px 6px; border-radius:8px; cursor:pointer; font-size:14px; position:relative; }
  label.op:hover { background:var(--surface2); }
  label.op input { position:absolute; opacity:0; pointer-events:none; }
  label.op .ck { flex:none; width:17px; height:17px; border:1.5px solid var(--mut); border-radius:5px; background:var(--surface); position:relative; }
  label.op input:checked + .ck { background:var(--verde); border-color:var(--verde); }
  label.op input:checked + .ck::after { content:""; position:absolute; left:4px; top:0; width:5px; height:10px; border:solid #fff; border-width:0 2px 2px 0; transform:rotate(45deg); }
  label.op input:focus-visible + .ck { outline:2px solid var(--argila); outline-offset:2px; }
  label.op .nome { flex:1; min-width:0; line-height:1.25; }
  label.op .n { font-size:12px; color:var(--mut); }
  label.op.zero { opacity:.45; }
  .mais-filtros { width:100%; margin-bottom:14px; }
  .fnota { font-size:11px; color:var(--mut); margin:2px 4px 14px; }
  .aviso-vazio { font-size:13px; color:var(--mut); padding:4px 2px 8px; }

  /* ---------- botões ---------- */
  .btn { padding:8px 16px; border:1px solid var(--line); background:var(--surface); color:var(--ink); border-radius:999px; cursor:pointer; font-size:13px; font-weight:600; }
  .btn:hover { border-color:var(--verde); color:var(--verde); }
  .btn.forte { background:var(--verde); border-color:var(--verde); color:#fff; }
  .btn.forte:hover { background:var(--verde-esc); color:#fff; }
  .btn.perigo { color:var(--err); }
  .btn.mini { padding:4px 11px; font-size:12px; }
  .btn.largo { width:100%; }

  /* ---------- abas e barras ---------- */
  .barra { display:flex; flex-wrap:wrap; gap:10px; align-items:center; justify-content:space-between; margin-bottom:14px; }
  .seg { display:inline-flex; background:var(--surface2); border:1px solid var(--line); border-radius:999px; padding:4px; gap:2px; flex-wrap:wrap; }
  .seg button { border:none; background:transparent; color:var(--mut); padding:8px 18px; border-radius:999px; font-size:14px; font-weight:600; cursor:pointer; }
  .seg button.on { background:var(--verde); color:#fff; }
  .seg .n { opacity:.75; font-weight:500; margin-left:4px; font-size:12px; }
  .btn-filtros { display:none; }
  .janela { background:var(--surface); border:1px solid var(--line); border-radius:var(--raio); padding:14px 20px 10px; margin:0 0 14px; }
  .janela-topo { font-size:14px; color:var(--mut); margin-bottom:6px; }
  .janela-topo b { color:var(--ink); font-size:15px; }
  #janela-range { width:100%; accent-color:var(--verde); height:22px; cursor:pointer; }
  .janela-marcas { display:flex; justify-content:space-between; gap:2px; margin-top:2px; }
  .janela-marcas button { border:none; background:transparent; color:var(--mut); font-size:12px; font-weight:600; cursor:pointer; padding:4px 6px; border-radius:999px; }
  .janela-marcas button.on { background:var(--verde-claro); color:var(--verde-esc); }
  .busca-linha { display:flex; flex-wrap:wrap; gap:10px; margin-bottom:6px; }
  .busca-linha input[type=search] { flex:1; min-width:220px; padding:11px 18px; font-size:15px; border:1px solid var(--line); border-radius:999px; background:var(--surface); color:var(--ink); }
  .busca-linha select { padding:10px 16px; font-size:14px; border:1px solid var(--line); border-radius:999px; background:var(--surface); color:var(--ink); }
  .count { color:var(--mut); font-size:13px; margin:12px 4px; }

  /* ---------- cartões ---------- */
  h2.dia { font-family:var(--serif); font-size:15px; font-weight:600; color:var(--verde); margin:26px 4px 12px; display:flex; align-items:center; gap:12px; }
  h2.dia::after { content:""; flex:1; height:1px; background:var(--line); }
  .card { background:var(--surface); border:1px solid var(--line); border-radius:var(--raio); padding:18px 22px 14px; margin-bottom:14px; transition:border-color .12s; }
  .card:hover { border-color:var(--verde); }
  .card-top { display:flex; justify-content:space-between; gap:12px; align-items:flex-start; font-size:13px; }
  .rv { display:flex; flex-wrap:wrap; gap:8px; align-items:center; min-width:0; }
  .rev { font-weight:700; color:var(--verde); }
  .rev.mut { color:var(--mut); font-weight:500; }
  .sjr { background:var(--surface2); color:var(--ink); border-radius:999px; padding:1px 9px; font-size:12px; font-weight:600; white-space:nowrap; }
  .conf { background:var(--verde-claro); color:var(--verde-esc); border-radius:999px; padding:1px 9px; font-size:11.5px; font-weight:700; white-space:nowrap; }
  .data { color:var(--mut); font-weight:600; white-space:nowrap; font-size:13px; }
  .titulo { display:block; margin:8px 0 4px; font-family:var(--serif); font-size:21px; line-height:1.3; font-weight:600; text-decoration:none; color:var(--ink); }
  .titulo:hover { color:var(--verde); text-decoration:underline; text-underline-offset:3px; }
  .autores { font-size:14px; color:var(--mut); }
  details.det { margin-top:10px; }
  details.det summary { cursor:pointer; font-size:13px; font-weight:600; color:var(--argila); list-style:none; }
  details.det summary::-webkit-details-marker { display:none; }
  details.det summary::before { content:"▸ "; }
  details.det[open] summary::before { content:"▾ "; }
  .det-in { margin-top:8px; }
  .res { font-size:14px; opacity:.9; }
  .tags { margin-bottom:8px; }
  .tag { display:inline-block; font-size:11.5px; background:var(--surface2); padding:2px 10px; border-radius:999px; margin:0 6px 4px 0; color:var(--mut); font-weight:600; }
  .acoes-card { display:flex; flex-wrap:wrap; gap:8px; align-items:center; margin-top:12px; padding-top:10px; border-top:1px solid var(--line); }
  .ac { display:inline-flex; align-items:center; gap:6px; border:1px solid var(--line); background:transparent; color:var(--mut); border-radius:999px; padding:5px 12px; font-size:12.5px; font-weight:600; cursor:pointer; text-decoration:none; }
  .ac svg { width:15px; height:15px; }
  .ac:hover { border-color:var(--verde); color:var(--verde); }
  .ac.on { background:var(--verde-claro); border-color:var(--verde); color:var(--verde-esc); }
  .ac.argila.on { background:var(--argila-claro); border-color:var(--argila); color:var(--argila); }
  .ac.ocupado { opacity:.55; pointer-events:none; }
  button.mais { display:block; margin:22px auto; padding:10px 26px; border-radius:999px; border:1px solid var(--verde); background:var(--surface); color:var(--verde); cursor:pointer; font-size:14px; font-weight:600; }
  footer { text-align:center; color:var(--mut); font-size:12px; padding:20px 20px 30px; }
  .vazio { text-align:center; color:var(--mut); padding:40px 10px; }

  /* ---------- configuração (1ª visita) ---------- */
  .modal-fundo { position:fixed; inset:0; background:rgba(25,20,12,.55); display:none; align-items:flex-start; justify-content:center; padding:4vh 14px; overflow:auto; z-index:50; }
  .modal-fundo.on { display:flex; }
  .modal { background:var(--surface); border-radius:18px; max-width:780px; width:100%; box-shadow:0 20px 60px rgba(0,0,0,.35); overflow:hidden; }
  .modal-topo { padding:24px 28px 14px; background:var(--verde-claro); }
  .modal-topo h2 { margin:0 0 6px; font-family:var(--serif); font-size:26px; color:var(--verde-esc); }
  .modal-topo p { margin:0; font-size:14px; color:var(--ink); opacity:.85; }
  .modal section { padding:18px 28px 6px; border-bottom:1px solid var(--line); }
  .modal h3 { margin:0 0 4px; font-family:var(--serif); font-size:18px; }
  .modal .dica { font-size:13px; color:var(--mut); margin:0 0 10px; }
  .modal input[type=text], .modal input[type=password] { width:100%; padding:10px 14px; font-size:14px; border:1px solid var(--line); border-radius:10px; background:var(--bg); color:var(--ink); }
  .entrada { display:flex; gap:8px; margin-bottom:10px; }
  .chips { display:flex; flex-wrap:wrap; gap:7px; margin:8px 0 12px; }
  .chip { display:inline-flex; align-items:center; gap:6px; padding:5px 12px; font-size:13px; border:1px solid var(--verde); border-radius:999px; background:var(--verde-claro); color:var(--verde-esc); font-weight:600; }
  .chip .x { cursor:pointer; opacity:.7; font-size:15px; line-height:1; border:none; background:transparent; color:inherit; padding:0; }
  .chip .x:hover { opacity:1; }
  .chip.sug { background:transparent; border:1px dashed var(--mut); color:var(--mut); cursor:pointer; }
  .chip.sug:hover { border-color:var(--verde); color:var(--verde); }
  .sug-titulo { font-size:12px; font-weight:700; letter-spacing:.06em; text-transform:uppercase; color:var(--mut); margin-top:4px; }
  .achados { margin:0 0 10px; }
  .achado { display:flex; justify-content:space-between; align-items:center; gap:10px; padding:8px 12px; border:1px solid var(--line); border-radius:10px; margin-bottom:6px; font-size:14px; }
  .achado small { color:var(--mut); display:block; }
  .campo { margin-bottom:12px; }
  .campo label { display:block; font-size:13px; font-weight:600; margin-bottom:4px; }
  .campo .ajuda { font-size:12px; color:var(--mut); margin-top:3px; }
  .ok-msg { color:var(--ok); font-size:13px; font-weight:600; }
  .err-msg { color:var(--err); font-size:13px; font-weight:600; }
  .modal-rodape { padding:16px 28px 22px; display:flex; gap:10px; flex-wrap:wrap; justify-content:flex-end; background:var(--surface); }

  .form-tema { background:var(--bg); border:1px solid var(--line); border-radius:12px; padding:14px 16px 6px; margin-bottom:14px; }
  .form-tema.editando { border-color:var(--argila); }
  .form-tema h4 { margin:0 0 10px; font-size:13px; letter-spacing:.06em; text-transform:uppercase; color:var(--verde); }
  .chip-input { display:flex; flex-wrap:wrap; gap:6px; align-items:center; padding:6px 8px; border:1px solid var(--line); border-radius:10px; background:var(--surface); min-height:44px; cursor:text; }
  .chip-input input { flex:1; min-width:170px; border:none !important; outline:none; background:transparent !important; padding:6px 4px !important; font-size:14px; color:var(--ink); width:auto !important; }
  .chip-input .chip { margin:0; }
  .acoes-form { display:flex; gap:8px; align-items:center; flex-wrap:wrap; margin:8px 0 10px; }
  .tema-card { display:flex; justify-content:space-between; align-items:center; gap:12px; border:1px solid var(--line); border-radius:12px; padding:10px 14px; margin-bottom:8px; background:var(--surface); }
  .tema-card.editando { border-color:var(--argila); background:var(--argila-claro); }
  .tema-info b { font-size:15px; }
  .tema-termos { font-size:12.5px; color:var(--mut); margin-top:2px; }
  .tema-acoes { display:flex; gap:6px; flex:none; }
  .previa { font-size:13px; color:var(--mut); margin:4px 0 8px; }
  .previa b { color:var(--ink); }
  .previa ul { margin:4px 0 0; padding-left:18px; }
  .ideias { margin:2px 0 10px; }
  .ideias .grupo { margin-bottom:8px; }
  .ideias .rot2 { font-size:12px; color:var(--mut); margin-bottom:4px; }
  .ideias .chips { margin:2px 0 4px; }
  .chip .cnt { font-weight:500; opacity:.7; font-size:12px; }
  .chip.zero { border-style:dashed; background:transparent; color:var(--mut); }
  .chip.generica { border-color:var(--argila); background:var(--argila-claro); color:var(--argila); }
  details.guia { margin:4px 0 12px; font-size:13px; background:var(--surface); border:1px solid var(--line); border-radius:10px; padding:8px 12px; }
  details.guia summary { cursor:pointer; font-weight:600; color:var(--argila); }
  details.guia ol { margin:8px 0 2px; padding-left:20px; }
  details.guia li { margin-bottom:5px; }
  .prompt-ia { margin-top:12px; padding-top:10px; border-top:1px solid var(--line); }
  .prompt-ia textarea { width:100%; font-family:ui-monospace,Menlo,Consolas,monospace; font-size:12.5px; line-height:1.45; padding:10px 12px; border:1px solid var(--line); border-radius:10px; background:var(--bg); color:var(--ink); resize:vertical; }
  .chip.termo { cursor:default; margin:0 4px 4px 0; }
  .link-ocultos { color:var(--argila); cursor:pointer; font-weight:600; text-decoration:underline; font-size:13px; }
  .motivo-lista { margin:6px 0 4px; padding-left:20px; font-size:14px; }
  .motivo-lista li { margin-bottom:7px; }
  .modal code { background:var(--surface2); padding:1px 6px; border-radius:6px; font-size:12.5px; }
  .modal section p { font-size:14px; margin:4px 0 8px; }
  .facet-linha { font-size:14px; margin:5px 0; }
  .oculto-linha { display:flex; justify-content:space-between; align-items:center; gap:10px; padding:8px 0; border-bottom:1px solid var(--line); font-size:14px; }
  .toast-area { position:fixed; right:18px; bottom:18px; display:flex; flex-direction:column; gap:8px; z-index:60; }
  .toast { background:var(--ink); color:var(--bg); padding:10px 16px; border-radius:12px; font-size:13px; max-width:340px; box-shadow:var(--sombra); }
  .toast.erro { background:var(--err); color:#fff; }

  @media (max-width: 860px) {
    .layout { grid-template-columns:minmax(0,1fr); gap:10px; }
    .sidebar { display:none; position:static; max-height:none; }
    .sidebar.aberta { display:block; }
    .btn-filtros { display:inline-block; }
    .marca h1 { font-size:24px; }
    .hero-in { padding-top:18px; }
    .hero-corpo { grid-template-columns:minmax(0,1fr); gap:14px; padding-top:14px; }
    .hero-foto { order:-1; justify-self:center; }
    .hero-foto img { max-height:min(var(--foto-altura),340px); max-width:100%; }
    .abelha-dia .cient { font-size:22px; }
    .titulo { font-size:19px; }
    .seg button { padding:7px 12px; font-size:13px; }
    .modal-topo, .modal section, .modal-rodape { padding-left:18px; padding-right:18px; }
  }
</style>
</head>
<body>
<header class="hero sem-foto" id="hero">
  <img class="hero-fundo" id="hero-fundo" alt="" aria-hidden="true" style="display:none">
  <div class="hero-sombra"></div>
  <div class="hero-in">
    <div class="marca">
      <svg width="46" height="46" viewBox="0 0 64 64" role="img" aria-label="Logo">
        <polygon points="32,4 57,18 57,46 32,60 7,46 7,18" fill="none" stroke="#fff" stroke-width="3" stroke-linejoin="round"/>
        <ellipse cx="25" cy="25" rx="6" ry="9" fill="#fff" opacity=".85" transform="rotate(-25 25 25)"/>
        <ellipse cx="37" cy="24" rx="6" ry="9" fill="#fff" opacity=".85" transform="rotate(20 37 24)"/>
        <ellipse cx="32" cy="38" rx="11" ry="8" fill="#fff"/>
        <rect x="26" y="30" width="3.5" height="16" fill="#3F4E2E" opacity=".75"/><rect x="34" y="30" width="3.5" height="16" fill="#3F4E2E" opacity=".75"/>
      </svg>
      <div><h1>__TITULO__</h1><div class="sub">__SUBTITULO__ · atualizado em __ATUALIZADO__</div></div>
    </div>
    <button class="btn-hero" onclick="abrirConfig(false)" title="Meus temas, revistas de confiança e conexões">⚙ Configurar</button>
  </div>
  <div class="hero-corpo">
    <div class="hero-legenda" id="hero-legenda"></div>
    <figure class="hero-foto" id="hero-foto" style="display:none" onclick="abrirFoto()" title="Clique para ampliar">
      <img id="hero-img" alt=""><span class="ampliar">🔍 Ampliar</span>
    </figure>
  </div>
</header>
<div class="lightbox" id="lightbox" onclick="fecharFoto()"><img id="lightbox-img" alt=""></div>

<div class="layout" id="layout">
  <aside class="sidebar" id="sidebar">
    <div id="sec-temas"></div>
    <div id="sec-conf"></div>
    <div id="sec-abelha"></div>
    <div class="sb-bloco">
      <div class="sb-titulo">Revista</div>
      <label class="op" style="margin-bottom:4px"><input type="checkbox" id="so-conf" onchange="setSoConf(this.checked)"><span class="ck"></span><span class="nome">Só revistas de confiança</span></label>
      <input type="search" id="rev-busca" placeholder="Buscar revista…" oninput="setRevBusca(this.value)">
      <div class="lista-op" id="rev-list"></div>
    </div>
    <button class="btn mais-filtros" id="btn-mais" onclick="alternarMais()">Mais filtros ▾</button>
    <div id="mais-dyn"></div>
    <div id="limpar-wrap"></div>
    <div id="ocultos-link" class="fnota"></div>
    <div class="fnota" id="fnota"></div>
  </aside>

  <main class="conteudo">
    <div class="barra">
      <div class="seg" id="seg">
        <button class="on" id="tab-novo" onclick="setAba('novo')">Novidades</button>
        <button id="tab-classico" onclick="setAba('classico')">Clássicos</button>
        <button id="tab-quero" onclick="setAba('quero')">Quero ler<span class="n" id="n-quero"></span></button>
        <button id="tab-lido" onclick="setAba('lido')">Lidos<span class="n" id="n-lido"></span></button>
      </div>
      <button class="btn btn-filtros" onclick="alternarSidebar()">☰ Filtros</button>
    </div>
    <div class="janela" id="area-janela">
      <div class="janela-topo">Publicados: <b id="janela-txt"></b></div>
      <input type="range" id="janela-range" min="0" max="3" step="1" value="1" oninput="setJanela(this.value)" aria-label="Período de publicação">
      <div class="janela-marcas" id="janela-marcas"></div>
    </div>
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
    <button class="mais" id="mais" onclick="mostrarMais()" style="display:none">Mostrar mais</button>
  </main>
</div>
<footer>Dados abertos do OpenAlex e do Europe PMC · SJR: SCImago Journal Rank · fotos: iNaturalist.</footer>

<div class="modal-fundo" id="modal"><div class="modal" id="modal-corpo" role="dialog" aria-modal="true"></div></div>
<div class="modal-fundo" id="modal-motivo" onclick="if(event.target===this)fecharMotivo()"><div class="modal" id="motivo-corpo" role="dialog" aria-modal="true"></div></div>
<div class="toast-area" id="toasts"></div>
<script>
const DADOS = __DADOS__;
const FILTROS_DEF = __FILTROS_DEF__;
const NOV_DIAS = __NOVDIAS__;
const JANELAS = __JANELAS__;
const PADRAO = __PADRAO__;
const FOTOS = __FOTOS__;
const FOTO_MODO = __FOTO_MODO__;
let FOTO = null;
const FILTROS = FILTROS_DEF.map(f => ({ nome: f.nome, opcoes: f.opcoes.map(o => o.nome).concat([f.rotulo_sem]) }));
const POR_PAGINA = 40;
const OA = 'https://api.openalex.org', ZOT = 'https://api.zotero.org';
const K_CFG = 'radar_cfg_v2', K_LEIT = 'radar_leitura_v1', K_LIVE = 'radar_live_v1', K_VISTO = 'radar_live_visto_v1', K_ZOT = 'radar_zotero_v1', K_OCULT = 'radar_ocultos_v1';

// ============================================================
//  Utilidades
// ============================================================
function lsGet(k, def) { try { const v = localStorage.getItem(k); return v ? JSON.parse(v) : def; } catch (e) { return def; } }
function lsSet(k, v) { try { localStorage.setItem(k, JSON.stringify(v)); } catch (e) {} }
function esc(s) {
  return String(s == null ? '' : s).replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
}
function fmtData(s) {
  if (!s) return '';
  const d = new Date(String(s).slice(0, 10) + 'T00:00:00');
  return isNaN(d) ? s : d.toLocaleDateString('pt-BR');
}
function norm(s) { return String(s || '').toLowerCase().normalize('NFD').replace(/[\u0300-\u036f]/g, '').replace(/[^a-z0-9]+/g, ' ').trim(); }
function hojeISO() { return new Date().toISOString().slice(0, 10); }
function diaISO(delta) { return new Date(Date.now() + delta * 86400000).toISOString().slice(0, 10); }
function seguroUrl(u) { return /^https?:\/\//i.test(u || '') ? u : '#'; }
function doiDe(url) { const m = String(url || '').match(/10\.\d{4,9}\/\S+/); return m ? m[0] : ''; }
function toast(msg, erro) {
  const a = document.getElementById('toasts'); if (!a) return;
  const e = document.createElement('div'); e.className = 'toast' + (erro ? ' erro' : ''); e.textContent = msg; a.appendChild(e);
  setTimeout(() => e.remove(), erro ? 7000 : 3500);
}
const valor = id => { const el = document.getElementById(id); return el ? (el.value || '').trim() : ''; };

// ============================================================
//  Configuração do usuário (fica neste navegador)
// ============================================================
const COLECAO_PADRAO = PADRAO.colecao || 'Radar de Abelhas';
let CFG = lsGet(K_CFG, null);
const PRIMEIRA_VEZ = !CFG;
if (!CFG) CFG = { topicos: [], revistas: [], openalexKey: '', zotero: { user: '', key: '', colecao: COLECAO_PADRAO } };
CFG.topicos = CFG.topicos || []; CFG.revistas = CFG.revistas || [];
CFG.zotero = Object.assign({ user: '', key: '', colecao: COLECAO_PADRAO }, CFG.zotero || {});
function salvarCfg() { lsSet(K_CFG, CFG); }
let seqId = Date.now();
const novoId = () => 't' + (seqId++);

// ============================================================
//  Itens: dados do robô + revistas de confiança buscadas ao vivo
// ============================================================
let ITENS = [], IDX = {}, LIVE = ((lsGet(K_LIVE, null) || {}).itens) || [];
const SJR_REV = {};
DADOS.forEach(d => { if (d.sjr != null && d.revista) SJR_REV[norm(d.revista)] = [d.sjr, d.q || '']; });
const RE_T = {};
function reTermo(t) { return RE_T[t] || (RE_T[t] = new RegExp('\\b' + String(t).toLowerCase().replace(/[.*+?^${}()|[\]\\]/g, '\\$&') + '(s|es)?\\b')); }
function casaTopico(d, tp) {
  if (tp.cfg && d.temas && d.temas.includes(tp.cfg)) return true;
  const t = ((d.titulo || '') + ' ' + (d.resumo || '')).toLowerCase();
  return (tp.termos || []).some(x => x && reTermo(x).test(t));
}
function indicesConf(d) {   // em quais das suas revistas de confiança este artigo foi publicado
  const out = [], n = norm(d.revista);
  const is = new Set((d.issn || []).map(x => String(x).replace('-', '').toUpperCase()));
  CFG.revistas.forEach((r, i) => { if ((n && norm(r.nome) === n) || (r.issns || []).some(x => is.has(String(x).replace('-', '').toUpperCase()))) out.push(i); });
  return out;
}
function recalcular() {
  ITENS.forEach(d => { d._m = CFG.topicos.filter(tp => casaTopico(d, tp)).map(tp => tp.id); d._cr = indicesConf(d); d._c = d._cr.length > 0; });
}
function montarItens() {
  const mapa = {};
  const add = d => {
    const k = d.tipo + '|' + d.key;
    const ts = (d.temas && d.temas.length) ? d.temas : (d.topico ? [d.topico] : []);
    if (mapa[k]) {
      ts.forEach(t => { if (!mapa[k].temas.includes(t)) mapa[k].temas.push(t); });
      if (d.completa) mapa[k].completa = true;
      if (d.issn && !mapa[k].issn) mapa[k].issn = d.issn;
      if (d.oa_url && !mapa[k].oa_url) mapa[k].oa_url = d.oa_url;
      return;
    }
    mapa[k] = Object.assign({}, d, { temas: ts.slice() });
  };
  DADOS.forEach(add); LIVE.forEach(add);
  ITENS = Object.values(mapa);
  IDX = {};
  ITENS.forEach(d => { if (!IDX[d.key] || d.tipo === 'novo') IDX[d.key] = d; });
  recalcular();
}

// ---- artigos vindos direto do OpenAlex (revistas de confiança) ----
function decodeAbstract(inv) {
  if (!inv) return '';
  const pos = [];
  Object.keys(inv).forEach(w => inv[w].forEach(i => { pos[i] = w; }));
  return pos.filter(x => x !== undefined).join(' ');
}
function limparDoi(d) { return String(d || '').replace(/^https?:\/\/(dx\.)?doi\.org\//i, ''); }
function facetasDe(r) {
  const tit = (r.titulo || '').toLowerCase(), tudo = tit + ' ' + (r.resumo || '').toLowerCase();
  const out = {};
  FILTROS_DEF.forEach(f => {
    const m = f.opcoes.filter(o => (o.termos || []).some(t => reTermo(t).test(tudo)) || (o.termos_titulo || []).some(t => reTermo(t).test(tit))).map(o => o.nome);
    out[f.nome] = m.length ? m : [f.rotulo_sem];
  });
  return out;
}
function recDeOA(w) {
  const src = ((w.primary_location || {}).source) || {};
  const autoresL = (w.authorships || []).map(a => (a.author || {}).display_name || '').filter(Boolean);
  const doi = limparDoi(w.doi);
  const titulo = String(w.display_name || w.title || '').replace(/<[^>]+>/g, '');
  const res = decodeAbstract(w.abstract_inverted_index);
  const issn = [].concat(src.issn || [], src.issn_l ? [src.issn_l] : []).filter((v, i, a) => a.indexOf(v) === i);
  const r = {
    key: doi ? 'doi:' + doi.toLowerCase() : 't:' + norm(titulo), titulo,
    autores: autoresL.slice(0, 6).join(', ') + (autoresL.length > 6 ? ' et al.' : ''),
    revista: src.display_name || '', issn, data: w.publication_date || '', ano: w.publication_year || null,
    resumo: res.length > 600 ? res.slice(0, 600).replace(/\s+\S*$/, '') + '…' : res,
    url: doi ? 'https://doi.org/' + doi : (w.id || ''), citacoes: w.cited_by_count || 0, tipo: 'novo', topico: 'Revistas de confiança', temas: [],
    oa: !!(w.open_access || {}).is_oa, oa_url: (w.open_access || {}).oa_url || '', fonte: 'OpenAlex', completa: true, _otipo: w.type || ''
  };
  r.facetas = facetasDe(r);
  r.motivo = { via: 'confianca', revista: r.revista };
  const hit = SJR_REV[norm(r.revista)];
  r.sjr = hit ? hit[0] : null; r.q = hit ? hit[1] : '';
  return r;
}
async function oaGet(caminho, params, chave) {
  const p = new URLSearchParams(params || {});
  const k = chave !== undefined ? chave : (CFG.openalexKey || '');
  if (k) p.set('api_key', k);
  const r = await fetch(OA + caminho + '?' + p.toString());
  if (!r.ok) throw new Error('OpenAlex respondeu ' + r.status + (r.status === 429 ? ' (limite de uso: crie uma chave grátis)' : ''));
  return r.json();
}
async function atualizarConfiaveis(forcar) {
  const rs = CFG.revistas.filter(r => (r.issns || []).length);
  if (!rs.length) { LIVE = []; lsSet(K_LIVE, { t: Date.now(), assin: '', itens: [] }); return; }
  const assin = rs.map(r => r.issns.join('|')).sort().join(';');
  const cache = lsGet(K_LIVE, null);
  if (!forcar && cache && cache.assin === assin && Date.now() - cache.t < 6 * 3600 * 1000) { LIVE = cache.itens || []; return; }
  const issns = [...new Set(rs.flatMap(r => r.issns))];
  const ini = diaISO(-30), fim = hojeISO(), brutos = [];
  for (let i = 0; i < issns.length; i += 25) {
    for (let pag = 1; pag <= 5; pag++) {
      const j = await oaGet('/works', {
        filter: 'primary_location.source.issn:' + issns.slice(i, i + 25).join('|') + ',type:article|review|preprint,from_publication_date:' + ini + ',to_publication_date:' + fim,
        sort: 'publication_date:desc', 'per-page': 100, page: pag });
      const lote = j.results || []; brutos.push(...lote);
      if (lote.length < 100) break;
    }
  }
  const visto = lsGet(K_VISTO, {}), hoje = hojeISO(), corteTardio = diaISO(-7);
  const itens = brutos.map(recDeOA).filter(r => ['article', 'review', 'preprint'].includes(r._otipo)).map(r => {
    delete r._otipo;
    if (!visto[r.key]) visto[r.key] = hoje;
    r.adicionado = visto[r.key]; r.tardio = (r.data || '').slice(0, 10) < corteTardio;
    return r;
  });
  const chaves = Object.keys(visto); if (chaves.length > 3000) chaves.slice(0, chaves.length - 3000).forEach(k => delete visto[k]);
  lsSet(K_VISTO, visto);
  LIVE = itens.slice(0, 600);
  lsSet(K_LIVE, { t: Date.now(), assin, itens: LIVE });
}
async function atualizarConfiaveisSeguro(forcar) {
  try { await atualizarConfiaveis(forcar); } catch (e) { toast('Não consegui atualizar as revistas de confiança: ' + (e.message || e), true); }
  montarItens(); render();
}

// ============================================================
//  Leitura (Quero ler / Lido) e Zotero
// ============================================================
let LEIT = lsGet(K_LEIT, {});
let OCULTOS = lsGet(K_OCULT, {});
function salvarLeit() { lsSet(K_LEIT, LEIT); }
const contar = st => Object.keys(LEIT).filter(k => LEIT[k].status === st).length;
function snapshot(d) {
  return { key: d.key, titulo: d.titulo, autores: d.autores, revista: d.revista, data: d.data, ano: d.ano, resumo: d.resumo,
           url: d.url, oa_url: d.oa_url || '', sjr: d.sjr == null ? null : d.sjr, q: d.q || '', citacoes: d.citacoes || 0 };
}
const zotOk = () => !!(CFG.zotero.user && CFG.zotero.key);
function zHdr(extra) { return Object.assign({ 'Zotero-API-Key': CFG.zotero.key, 'Zotero-API-Version': '3', 'Content-Type': 'application/json' }, extra || {}); }
function tokenEscrita() {
  const b = new Uint8Array(16);
  if (window.crypto && crypto.getRandomValues) crypto.getRandomValues(b); else for (let i = 0; i < 16; i++) b[i] = Math.floor(Math.random() * 256);
  return Array.from(b).map(x => x.toString(16).padStart(2, '0')).join('');
}
async function zFetch(caminho, opts) {
  const o = opts || {};
  const r = await fetch(ZOT + '/users/' + CFG.zotero.user + caminho, Object.assign({}, o, { headers: zHdr(o.headers) }));
  if (!r.ok && r.status !== 204) {
    const msg = r.status === 403 ? 'sem permissão (a chave precisa de acesso de escrita à sua biblioteca)' : r.status === 404 ? 'não encontrado'
      : r.status === 412 ? 'conflito de versão, tente de novo' : r.status === 429 ? 'muitas chamadas, tente em instantes' : 'erro ' + r.status;
    const e = new Error('Zotero: ' + msg); e.status = r.status; throw e;
  }
  return r;
}
async function zColecoes() {
  const cache = lsGet(K_ZOT, { itens: {}, col: null });
  if (cache.col && cache.col.user === CFG.zotero.user && cache.col.nome === CFG.zotero.colecao) return cache.col;
  let todas = [];
  for (let start = 0, n = 0; n < 20; n++, start += 100) {
    const lote = await (await zFetch('/collections?limit=100&start=' + start)).json();
    todas = todas.concat(lote); if (lote.length < 100) break;
  }
  const achar = (nome, pai) => todas.find(c => c.data.name === nome && (c.data.parentCollection || false) === (pai || false));
  const criar = async (nome, pai) => {
    const j = await (await zFetch('/collections', { method: 'POST', headers: { 'Zotero-Write-Token': tokenEscrita() },
      body: JSON.stringify([{ name: nome, parentCollection: pai || false }]) })).json();
    const ok = (j.successful || {})['0']; if (!ok) throw new Error('Zotero não criou a pasta "' + nome + '"');
    return ok.key || (ok.data && ok.data.key);
  };
  const raiz = achar(CFG.zotero.colecao, false), kraiz = raiz ? raiz.key : await criar(CFG.zotero.colecao, false);
  const q = achar('Quero ler', kraiz), kq = q ? q.key : await criar('Quero ler', kraiz);
  const l = achar('Lido', kraiz), kl = l ? l.key : await criar('Lido', kraiz);
  const col = { user: CFG.zotero.user, nome: CFG.zotero.colecao, raiz: kraiz, quero: kq, lido: kl };
  cache.col = col; lsSet(K_ZOT, cache); return col;
}
async function metadadosZotero(d) {
  const doi = doiDe(d.url); let w = null;
  if (doi) { try { w = await oaGet('/works/https://doi.org/' + doi, {}); } catch (e) { w = null; } }
  const nomes = w ? (w.authorships || []).map(a => (a.author || {}).display_name).filter(Boolean)
                  : String(d.autores || '').replace(/ et al\.$/, '').split(/,\s+/).filter(Boolean);
  const creators = nomes.map(n => { const p = n.trim().split(/\s+/); return p.length > 1
    ? { creatorType: 'author', firstName: p.slice(0, -1).join(' '), lastName: p[p.length - 1] } : { creatorType: 'author', name: n }; });
  const src = w ? ((w.primary_location || {}).source || {}) : {};
  return { itemType: 'journalArticle', title: d.titulo, creators, abstractNote: w ? decodeAbstract(w.abstract_inverted_index) : (d.resumo || ''),
           publicationTitle: d.revista || '', date: (d.data || '').slice(0, 10), DOI: doi, url: d.url || '', ISSN: src.issn_l || '',
           tags: [{ tag: COLECAO_PADRAO }] };
}
async function zItemExistente(d) {
  const doi = doiDe(d.url); if (!doi) return null;
  const l = await (await zFetch('/items?q=' + encodeURIComponent(doi) + '&qmode=everything&limit=5')).json();
  const it = l.find(x => ((x.data || {}).DOI || '').toLowerCase() === doi.toLowerCase());
  return it ? it.key : null;
}
async function zAtualizarColecoes(itemKey, fn) {
  const it = await (await zFetch('/items/' + itemKey)).json();
  const atual = (it.data.collections || []).slice(), novo = fn(atual.slice());
  if (JSON.stringify(novo.slice().sort()) === JSON.stringify(atual.slice().sort())) return;
  await zFetch('/items/' + itemKey, { method: 'PATCH', headers: { 'If-Unmodified-Since-Version': String(it.version) }, body: JSON.stringify({ collections: novo }) });
}
async function sincronizarZotero(d, status) {   // status: 'quero' | 'lido' | 'raiz' | '' (tirar das pastas de leitura)
  const col = await zColecoes(), cache = lsGet(K_ZOT, { itens: {}, col });
  const destino = status === 'quero' ? col.quero : status === 'lido' ? col.lido : status === 'raiz' ? col.raiz : null;
  let itemKey = (cache.itens || {})[d.key] || await zItemExistente(d);
  const ajustar = arr => {
    if (status === 'raiz') { if (!arr.includes(col.raiz)) arr.push(col.raiz); return arr; }
    arr = arr.filter(k => k !== col.quero && k !== col.lido);
    if (destino) arr.push(destino);
    return arr;
  };
  if (!itemKey) {
    if (!destino) return;
    const meta = await metadadosZotero(d);
    const j = await (await zFetch('/items', { method: 'POST', headers: { 'Zotero-Write-Token': tokenEscrita() },
      body: JSON.stringify([Object.assign(meta, { collections: [destino] })]) })).json();
    const ok = (j.successful || {})['0']; if (!ok) throw new Error('Zotero não criou o item');
    itemKey = ok.key || (ok.data && ok.data.key);
  } else await zAtualizarColecoes(itemKey, ajustar);
  cache.itens = cache.itens || {}; cache.itens[d.key] = itemKey; cache.col = col; lsSet(K_ZOT, cache);
}
const EM_ANDAMENTO = new Set();
async function marcar(key, status) {
  if (EM_ANDAMENTO.has(key)) return;
  const d = IDX[key] || (LEIT[key] && LEIT[key].snap); if (!d) return;
  const atual = (LEIT[key] || {}).status, novo = atual === status ? '' : status;
  if (novo) LEIT[key] = Object.assign({}, LEIT[key] || {}, { status: novo, snap: snapshot(d), quando: hojeISO() }); else delete LEIT[key];
  salvarLeit(); render();
  if (!zotOk()) { if (novo) toast('Marcado aqui. Conecte o Zotero (⚙) para enviar à sua biblioteca.'); return; }
  EM_ANDAMENTO.add(key);
  try {
    await sincronizarZotero(d, novo);
    toast(novo ? 'Salvo no Zotero em "' + (novo === 'quero' ? 'Quero ler' : 'Lido') + '".' : 'Tirado das pastas de leitura no Zotero.');
  } catch (e) { toast(e.message || 'Não consegui falar com o Zotero.', true); }
  finally { EM_ANDAMENTO.delete(key); render(); }
}
async function enviarZotero(key) {
  if (!zotOk()) { toast('Conecte o Zotero primeiro: ⚙ Meus temas e revistas > Conexões.', true); return; }
  if (EM_ANDAMENTO.has(key)) return;
  const d = IDX[key] || (LEIT[key] && LEIT[key].snap); if (!d) return;
  EM_ANDAMENTO.add(key);
  try { await sincronizarZotero(d, 'raiz'); toast('Adicionado ao Zotero na pasta "' + CFG.zotero.colecao + '".'); }
  catch (e) { toast(e.message || 'Não consegui falar com o Zotero.', true); }
  finally { EM_ANDAMENTO.delete(key); render(); }
}

// ============================================================
//  Filtros e lista
// ============================================================
let aba = 'novo', busca = '', limite = POR_PAGINA;
let revistasSel = [], fac = {}, periodo = '', quartil = '', ordem = 'padrao', revBusca = '', maisAberto = false, soConf = false;
let janelaIdx = Math.max(0, JANELAS.indexOf(NOV_DIAS)), corteJanela = '', ZIT = {};
const TEM_SJR = DADOS.some(d => d.sjr != null);
const ROT_LONGO = { 3: 'últimos 3 dias', 7: 'última semana', 15: 'últimos 15 dias (quinzena)', 30: 'último mês', 60: 'últimos 2 meses', 90: 'últimos 3 meses', 180: 'últimos 6 meses', 365: 'último ano', 0: 'todo o histórico guardado' };
const ROT_CURTO = { 3: '3 d', 7: '1 sem', 15: '15 d', 30: '1 mês', 60: '2 m', 90: '3 m', 180: '6 m', 365: '1 ano', 0: 'Tudo' };
const rotL = n => ROT_LONGO[n] || ('últimos ' + n + ' dias');
const rotC = n => ROT_CURTO[n] || (n + ' d');
const ICO = {
  livro: '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M2 4h6a4 4 0 0 1 4 4v13a3 3 0 0 0-3-3H2z"/><path d="M22 4h-6a4 4 0 0 0-4 4v13a3 3 0 0 1 3-3h7z"/></svg>',
  check: '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="9"/><path d="M8 12.5l2.7 2.7L16 9.5"/></svg>',
  zot: '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><rect x="3" y="3" width="18" height="18" rx="3"/><path d="M12 8v8M8 12h8"/></svg>',
  info: '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="9"/><path d="M12 11v5M12 8h.01"/></svg>',
  aberto: '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><rect x="4" y="11" width="16" height="10" rx="2"/><path d="M8 11V7a4 4 0 0 1 7.5-2"/></svg>'
};
function rotMes(ym) {
  const dt = new Date(ym + '-01T00:00:00');
  if (isNaN(dt)) return ym;
  const t = dt.toLocaleDateString('pt-BR', { month: 'long', year: 'numeric' });
  return t.charAt(0).toUpperCase() + t.slice(1);
}
function setJanela(i) { janelaIdx = parseInt(i, 10) || 0; limite = POR_PAGINA; render(); }
function passaJanela(d) {
  if (!corteJanela) return true;
  let ref = (d.data || d.adicionado || '').slice(0, 10);
  if (d.tardio && d.adicionado && d.adicionado > ref) ref = d.adicionado.slice(0, 10);
  return !ref || ref >= corteJanela;
}
function renderJanela() {
  const el = document.getElementById('area-janela');
  el.style.display = aba === 'novo' ? 'block' : 'none';
  if (aba !== 'novo') { corteJanela = ''; return; }
  const dias = JANELAS[janelaIdx];
  corteJanela = dias ? new Date(Date.now() - dias * 86400000).toISOString().slice(0, 10) : '';
  document.getElementById('janela-txt').textContent = rotL(dias);
  const r = document.getElementById('janela-range');
  r.max = JANELAS.length - 1; r.value = janelaIdx;
  document.getElementById('janela-marcas').innerHTML = JANELAS.map((n, i) =>
    '<button type="button" class="' + (i === janelaIdx ? 'on' : '') + '" onclick="setJanela(' + i + ')">' + rotC(n) + '</button>').join('');
}
const textoDe = d => d._t || (d._t = ((d.titulo || '') + ' ' + (d.autores || '') + ' ' + (d.resumo || '') + ' ' + (d.revista || '')).toLowerCase());
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
  if (quartil === 'com') return d.sjr != null;
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
function setSoConf(v) { soConf = !!v; limite = POR_PAGINA; render(); }
function alternarMais() { maisAberto = !maisAberto; render(); }
function alternarSidebar() { document.getElementById('sidebar').classList.toggle('aberta'); }
function alternarSel(arr, v) { const k = arr.indexOf(v); if (k >= 0) arr.splice(k, 1); else arr.push(v); }
function limparFiltros() {
  revistasSel = []; fac = {}; periodo = ''; quartil = ''; busca = ''; revBusca = ''; soConf = false;
  document.getElementById('busca').value = ''; document.getElementById('rev-busca').value = ''; document.getElementById('so-conf').checked = false;
  limite = POR_PAGINA; render();
}
function mostrarMais() { limite += POR_PAGINA; render(); }
function fmtSjr(v) { return (Math.round(v * 100) / 100).toFixed(2); }

function cabecalhoCard(d, dataTxt) {
  const sjr = d.sjr != null ? '<span class="sjr" title="SCImago Journal Rank (SJR) da revista">SJR ' + fmtSjr(d.sjr) + (d.q ? ' · ' + esc(d.q) : '') + '</span>' : '';
  const conf = d._c ? '<span class="conf" title="Uma das suas revistas de confiança">confiança</span>' : '';
  return '<div class="card-top"><div class="rv">' +
    (d.revista ? '<span class="rev">' + esc(d.revista) + '</span>' : '<span class="rev mut">Revista não informada</span>') + sjr + conf +
    '</div><span class="data">' + esc(dataTxt) + '</span></div>';
}
function acoesHtml(d) {
  const st = (LEIT[d.key] || {}).status, z = ZIT[d.key], k = esc(d.key);
  return '<div class="acoes-card">' +
    '<button class="ac' + (st === 'quero' ? ' on' : '') + '" data-acao="quero" data-k="' + k + '" title="Guardar em Quero ler">' + ICO.livro + 'Quero ler</button>' +
    '<button class="ac argila' + (st === 'lido' ? ' on' : '') + '" data-acao="lido" data-k="' + k + '" title="Marcar como lido">' + ICO.check + 'Lido</button>' +
    '<button class="ac' + (z ? ' on' : '') + '" data-acao="zotero" data-k="' + k + '" title="Adicionar ao Zotero">' + ICO.zot + (z ? 'No Zotero' : 'Zotero') + '</button>' +
    '<button class="ac" data-acao="motivo" data-k="' + k + '" title="Ver por que este artigo entrou">' + ICO.info + 'Por que entrou?</button>' +
    (d.oa_url ? '<a class="ac" href="' + esc(seguroUrl(d.oa_url)) + '" target="_blank" rel="noopener" title="Versão de acesso aberto">' + ICO.aberto + 'Texto livre</a>' : '') +
    '</div>';
}
function itemHtml(d) {
  const dataTxt = aba === 'classico'
    ? [d.ano || fmtData(d.data), (d.citacoes || 0) + ' citações'].filter(Boolean).join(' · ')
    : (fmtData(d.data) || String(d.ano || '')) + (d.tardio && d.adicionado ? ' · chegou ao radar em ' + fmtData(d.adicionado) : '');
  const tags = (d._m || []).map(id => { const t = CFG.topicos.find(x => x.id === id); return t ? '<span class="tag">' + esc(t.nome) + '</span>' : ''; }).join('');
  return '<article class="card">' + cabecalhoCard(d, dataTxt) +
    '<a class="titulo" href="' + esc(seguroUrl(d.url)) + '" target="_blank" rel="noopener">' + esc(d.titulo) + '</a>' +
    '<div class="autores">' + esc(d.autores) + '</div>' +
    '<details class="det"><summary>Resumo e detalhes</summary><div class="det-in"><div class="tags">' + tags + '</div>' +
    '<div class="res">' + (d.resumo ? esc(d.resumo) : '<i>(sem resumo disponível: a editora não libera)</i>') + '</div></div></details>' +
    acoesHtml(d) + '</article>';
}
function checks(itens, tipo, f) {
  return itens.map(o => '<label class="op' + (o.n === 0 && !o.on ? ' zero' : '') + '"><input type="checkbox" data-tipo="' + tipo +
    '" data-f="' + esc(f || '') + '" data-o="' + esc(o.id != null ? o.id : o.nome) + '"' + (o.on ? ' checked' : '') + '><span class="ck"></span>' +
    '<span class="nome">' + esc(o.nome) + '</span><span class="n">' + o.n + '</span></label>').join('');
}
function ordenar(xs) {
  const padrao = (a, b) => aba === 'novo'
    ? ((b.data || b.adicionado || '').localeCompare(a.data || a.adicionado || '') || (b.adicionado || '').localeCompare(a.adicionado || ''))
    : ((b.citacoes || 0) - (a.citacoes || 0));
  return xs.slice().sort((a, b) => {
    if (ordem === 'sjr') return ((b.sjr != null ? b.sjr : -1) - (a.sjr != null ? a.sjr : -1)) || padrao(a, b);
    if (ordem === 'cit') return ((b.citacoes || 0) - (a.citacoes || 0)) || padrao(a, b);
    if (ordem === 'data') return ((b.data || String(b.ano || '')).localeCompare(a.data || String(a.ano || ''))) || padrao(a, b);
    return padrao(a, b);
  });
}
function escolherFoto() {
  if (!FOTOS.length) return null;
  if (FOTO_MODO === 'dia') return FOTOS[Math.floor(Date.now() / 86400000) % FOTOS.length];
  const ult = lsGet('radar_foto_ultima_v1', -1);
  let i = Math.floor(Math.random() * FOTOS.length);
  if (FOTOS.length > 1 && i === ult) i = (i + 1 + Math.floor(Math.random() * (FOTOS.length - 1))) % FOTOS.length;   // nunca repete a foto anterior
  lsSet('radar_foto_ultima_v1', i);
  return FOTOS[i];
}
function renderHero() {
  FOTO = escolherFoto();
  const leg = document.getElementById('hero-legenda'), img = document.getElementById('hero-img'), fundo = document.getElementById('hero-fundo');
  const fig = document.getElementById('hero-foto'), hero = document.getElementById('hero');
  const semFoto = () => { fig.style.display = 'none'; fundo.style.display = 'none'; hero.classList.add('sem-foto'); };
  if (FOTO && FOTO.url) {
    img.src = FOTO.url; fundo.src = FOTO.url; img.alt = FOTO.nome_cientifico || 'Abelha';
    fig.style.display = 'block'; fundo.style.display = 'block'; hero.classList.remove('sem-foto');
    img.onerror = semFoto;
    leg.innerHTML = '<div class="abelha-dia"><div class="rot">' + (FOTO_MODO === 'dia' ? 'Abelha do dia' : 'Uma abelha ao acaso') + '</div><div class="cient">' + esc(FOTO.nome_cientifico) + '</div>' +
      (FOTO.nome_popular ? '<div class="pop">' + esc(FOTO.nome_popular) + '</div>' : '') + '</div>' +
      '<div class="credito">Foto: ' + esc(FOTO.credito || '') + ' · <a href="' + esc(seguroUrl(FOTO.link)) + '" target="_blank" rel="noopener">iNaturalist</a></div>';
  } else { semFoto(); leg.innerHTML = ''; }
}
function abrirFoto() {
  if (!FOTO || !FOTO.url) return;
  document.getElementById('lightbox-img').src = FOTO.url; document.getElementById('lightbox').classList.add('on');
}
function fecharFoto() { document.getElementById('lightbox').classList.remove('on'); }
document.addEventListener('keydown', e => { if (e.key === 'Escape') { fecharFoto(); fecharMotivo(); } });
// ============================================================
//  "Por que entrou?" e artigos ocultados
// ============================================================
function motivoDe(d) {
  if (d.motivo) return d.motivo;
  const t = (d.titulo || '').toLowerCase(), a = (d.resumo || '').toLowerCase(), ach = [];
  (PADRAO.termos_abelha || []).forEach(x => {
    const lug = []; if (reTermo(x).test(t)) lug.push('título'); if (reTermo(x).test(a)) lug.push('resumo');
    if (lug.length) ach.push([x, lug.join('+')]);
  });
  return { via: d.completa ? 'revista' : 'busca', achou: ach, revista: d.revista, antigo: true };
}
const chipTermo = (t, lugar) => '<span class="chip termo">' + esc(t) + (lugar ? ' <span class="cnt">' + esc(String(lugar).replace(/\+/g, ' e ')) + '</span>' : '') + '</span>';
function porqueChegou(d, m) {
  if (m.via === 'revista') return 'Veio por ser uma <b>revista só de abelhas</b> da lista do robô (<i>' + esc(m.revista || d.revista) + '</i>): entra tudo o que ela publica, sem olhar palavras.';
  if (m.via === 'confianca') return 'Veio da busca <b>ao vivo</b> da sua revista de confiança <i>' + esc(m.revista) + '</i>: entra tudo o que ela publica.';
  if (m.via === 'classico') {
    const p = (m.termos || []).concat(m.contexto || []);
    return 'É um <b>clássico</b> do tema <b>' + esc(m.tema) + '</b> (um dos mais citados, ' + (m.citacoes || 0) + ' citações).' + (p.length ? ' Palavras: ' + p.map(x => chipTermo(x)).join('') : '');
  }
  if (m.via === 'tema') return 'Busca por tema (modo antigo): tema <b>' + esc(m.tema) + '</b>, pontuação ' + (m.pontos != null ? m.pontos : '?') + '.';
  const ach = m.achou || [];
  if (ach.length) return 'Busca por <b>palavras de abelha</b>: encontrou ' + ach.map(x => chipTermo(x[0], x[1])).join('') + '.';
  return 'Busca por palavras de abelha, mas <b>nenhuma delas aparece escrita</b> no título nem no resumo carregados. O OpenAlex achou por uma variação da palavra, pelas palavras-chave ou por um trecho do resumo que não está aqui. <b>É um bom candidato a ser irrelevante.</b>';
}
function porqueNoFeed(d) {
  const ativos = CFG.topicos.filter(t => t.ativo);
  if (!ativos.length) return 'Você não marcou nenhum tema, então o site mostra tudo.';
  const txt = ((d.titulo || '') + ' ' + (d.resumo || '')).toLowerCase();
  const casados = ativos.filter(t => (d._m || []).includes(t.id)).map(t => ({ nome: t.nome, termos: (t.termos || []).filter(x => reTermo(x).test(txt)).slice(0, 5) }));
  const marcadas = (d._cr || []).filter(i => CFG.revistas[i] && CFG.revistas[i].mostrar).map(i => CFG.revistas[i].nome);
  let h = '';
  if (casados.length) h += 'Combina com o tema marcado: ' + casados.map(c => '<b>' + esc(c.nome) + '</b> ' + (c.termos.length ? c.termos.map(x => chipTermo(x)).join('') : '<span class="dica">(pelas etiquetas do robô)</span>')).join(' ') + '.';
  if (marcadas.length) h += ' Também aparece porque você marcou a revista de confiança <b>' + marcadas.map(esc).join(', ') + '</b>.';
  return h || 'Hoje ele não passaria pelos temas marcados: você deve estar vendo este artigo em uma das suas listas (Quero ler / Lidos).';
}
function porqueClassificado(d) {
  const tit = (d.titulo || '').toLowerCase(), tudo = tit + ' ' + (d.resumo || '').toLowerCase();
  return FILTROS_DEF.map(f => {
    const ops = (d.facetas && d.facetas[f.nome]) || [];
    const partes = ops.map(op => {
      const o = f.opcoes.find(x => x.nome === op);
      const termos = o ? (o.termos || []).filter(t => reTermo(t).test(tudo)).concat((o.termos_titulo || []).filter(t => reTermo(t).test(tit))).slice(0, 4) : [];
      return '<b>' + esc(op) + '</b> ' + (termos.length ? termos.map(t => chipTermo(t)).join('') : (o ? '<span class="dica">(palavra no resumo completo, fora do trecho carregado)</span>' : '<span class="dica">(nenhuma palavra encontrada)</span>'));
    });
    return '<div class="facet-linha">' + esc(f.nome) + ': ' + (partes.join(' · ') || '—') + '</div>';
  }).join('') || '<p class="dica">Sem categorias configuradas.</p>';
}
function abrirMotivo(key) {
  const d = IDX[key] || (LEIT[key] && LEIT[key].snap); if (!d) return;
  const m = motivoDe(d);
  document.getElementById('motivo-corpo').innerHTML =
    '<div class="modal-topo"><h2>Por que este artigo está aqui?</h2><p>' + esc(d.titulo) + '</p></div>' +
    '<section><h3>1. Como ele chegou ao radar</h3><p>' + porqueChegou(d, m) + '</p>' +
    (m.antigo ? '<p class="dica">Refeito agora com o título e o trecho do resumo carregados, porque este artigo é anterior ao registro de motivos.</p>' : '') +
    (m.fonte ? '<p class="dica">Fonte: ' + esc(m.fonte) + '</p>' : '') + '</section>' +
    '<section><h3>2. Por que ele aparece no seu feed</h3><p>' + porqueNoFeed(d) + '</p></section>' +
    '<section><h3>3. Como foi classificado</h3>' + porqueClassificado(d) + '</section>' +
    '<section><h3>Não tem a ver com abelhas?</h3><ul class="motivo-lista">' +
    '<li>Se a palavra encontrada tem outro sentido (por exemplo <i>bee</i> em <i>bee-eater</i>, um pássaro), bloqueie-a no título com <code>excluir &gt; termos</code> no <code>config.yaml</code> (ex.: <code>bee-eater</code>) ou tire-a de <code>abelhas &gt; termos</code>.</li>' +
    '<li>Para exigir mais de toda a busca, use <code>abelhas &gt; rigor: medio</code> ou <code>alto</code>.</li>' +
    '<li>"Ocultar" guarda o artigo como irrelevante só no seu navegador. O painel "Ocultos" mostra quais palavras mais trouxeram artigos que você ocultou.</li></ul></section>' +
    '<div class="modal-rodape"><button class="btn perigo" data-k="' + esc(d.key) + '" onclick="ocultar(this.dataset.k)">Não é sobre abelhas: ocultar</button><button class="btn forte" onclick="fecharMotivo()">Fechar</button></div>';
  document.getElementById('modal-motivo').classList.add('on');
}
function fecharMotivo() { const m = document.getElementById('modal-motivo'); if (m) m.classList.remove('on'); }
function ocultar(key) {
  const d = IDX[key] || (LEIT[key] && LEIT[key].snap); if (!d) return;
  const m = motivoDe(d);
  OCULTOS[key] = { titulo: d.titulo, revista: d.revista || '', via: m.via, termos: (m.achou || []).map(x => x[0]), quando: hojeISO() };
  lsSet(K_OCULT, OCULTOS); fecharMotivo(); render();
  toast('Artigo ocultado. Para desfazer, abra "Ocultos" na barra lateral.');
}
function restaurar(key) { delete OCULTOS[key]; lsSet(K_OCULT, OCULTOS); render(); if (Object.keys(OCULTOS).length) abrirOcultos(); else fecharMotivo(); }
function statsOcultos() {
  const c = {}; Object.values(OCULTOS).forEach(o => (o.termos || []).forEach(t => { c[t] = (c[t] || 0) + 1; }));
  return Object.keys(c).map(t => [t, c[t]]).sort((a, b) => b[1] - a[1]);
}
function abrirOcultos() {
  const ks = Object.keys(OCULTOS).sort((a, b) => (OCULTOS[b].quando || '').localeCompare(OCULTOS[a].quando || '')), st = statsOcultos();
  document.getElementById('motivo-corpo').innerHTML =
    '<div class="modal-topo"><h2>Artigos ocultados (' + ks.length + ')</h2><p>Eles ficam escondidos só neste navegador. Restaure se escondeu sem querer.</p></div>' +
    '<section><h3>Palavras que mais trouxeram artigos ocultados</h3>' + (st.length
      ? '<p>' + st.slice(0, 12).map(x => chipTermo(x[0], x[1] + '×')).join('') + '</p><p class="dica">Se uma palavra aparece muito aqui, ela pode estar trazendo artigos fora do assunto. Revise-a em <code>abelhas &gt; termos</code> do <code>config.yaml</code>, ou bloqueie um termo problemático em <code>excluir &gt; termos</code>.</p>'
      : '<p class="dica">Ainda não há palavras registradas (os artigos ocultados vieram de revistas inteiras ou de clássicos).</p>') + '</section>' +
    '<section><h3>Lista</h3>' + (ks.map(k => '<div class="oculto-linha"><div><b>' + esc(OCULTOS[k].titulo) + '</b><div class="dica" style="margin:0">' + esc(OCULTOS[k].revista) + '</div></div><button class="btn mini" data-k="' + esc(k) + '" onclick="restaurar(this.dataset.k)">Restaurar</button></div>').join('') || '<p class="dica">Nenhum.</p>') + '</section>' +
    '<div class="modal-rodape"><button class="btn forte" onclick="fecharMotivo()">Fechar</button></div>';
  document.getElementById('modal-motivo').classList.add('on');
}

function renderLeitura() {
  const chaves = Object.keys(LEIT).filter(k => LEIT[k].status === aba).sort((a, b) => (LEIT[b].quando || '').localeCompare(LEIT[a].quando || ''));
  document.getElementById('count').textContent = chaves.length + (aba === 'quero' ? ' artigo(s) para ler' : ' artigo(s) lido(s)');
  document.getElementById('lista').innerHTML = chaves.length
    ? chaves.map(k => itemHtml(Object.assign({}, LEIT[k].snap, IDX[k] || {}))).join('')
    : '<div class="vazio">Nada aqui ainda. Use os botões "Quero ler" e "Lido" nos cartões dos artigos.</div>';
  document.getElementById('mais').style.display = 'none';
}

function render() {
  const leit = aba === 'quero' || aba === 'lido';
  ['novo', 'classico', 'quero', 'lido'].forEach(x => document.getElementById('tab-' + x).classList.toggle('on', aba === x));
  document.getElementById('n-quero').textContent = contar('quero') || '';
  document.getElementById('n-lido').textContent = contar('lido') || '';
  document.getElementById('layout').classList.toggle('leitura', leit);
  document.getElementById('area-busca').style.display = leit ? 'none' : 'flex';
  renderJanela();
  ZIT = (lsGet(K_ZOT, { itens: {} }).itens) || {};
  if (leit) { renderLeitura(); return; }

  const base = ITENS.filter(d => d.tipo === aba && !OCULTOS[d.key]);
  const nOc = Object.keys(OCULTOS).length;
  document.getElementById('ocultos-link').innerHTML = nOc ? '<a class="link-ocultos" onclick="abrirOcultos()">Ocultos (' + nOc + ')</a>' : '';
  const ativos = CFG.topicos.filter(t => t.ativo);
  const passaTema = d => !ativos.length || ativos.some(t => (d._m || []).includes(t.id)) || (d._cr || []).some(i => CFG.revistas[i] && CFG.revistas[i].mostrar);
  const passaTudo = (d, ig) => {
    if (ig !== 'tema' && !passaTema(d)) return false;
    if (soConf && !d._c) return false;
    if (ig !== 'rev' && revistasSel.length && !revistasSel.includes(d.revista)) return false;
    if (!passaJanela(d)) return false;
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
  const secao = (titulo, corpo, extra) => '<div class="sb-bloco"><div class="sb-titulo"><span>' + esc(titulo) + '</span>' + (extra || '') + '</div>' + corpo + '</div>';
  const facetaHtml = f => {
    const arr = filtrar('f:' + f.nome), sel = fac[f.nome] || [];
    return secao(f.nome, '<div class="lista-op">' + checks(f.opcoes.map(o => ({
      nome: o, n: arr.filter(d => opcoesDe(d, f.nome).includes(o)).length, on: sel.includes(o) })), 'faceta', f.nome) + '</div>');
  };

  // Meus temas
  const arrT = filtrar('tema');
  document.getElementById('sec-temas').innerHTML = CFG.topicos.length
    ? secao('Meus temas', '<div class="lista-op">' + checks(CFG.topicos.map(t => ({
        id: t.id, nome: t.nome, n: arrT.filter(d => (d._m || []).includes(t.id)).length, on: !!t.ativo })), 'tema') + '</div>' +
        '', '<a onclick="abrirConfig(false)">Editar</a>')
    : secao('Meus temas', '<div class="aviso-vazio">Você ainda não escolheu temas, então o site mostra tudo. Escolha os seus para filtrar.</div>',
        '<a onclick="abrirConfig(false)">Escolher</a>');
  document.getElementById('sec-conf').innerHTML = CFG.revistas.length
    ? secao('Revistas de confiança', '<div class="lista-op">' + checks(CFG.revistas.map((r, i) => ({
        id: i, nome: r.nome, n: arrT.filter(d => (d._cr || []).includes(i)).length, on: !!r.mostrar })), 'conf') + '</div>' +
        '<div class="fnota" style="margin:4px 2px 8px">' + (ativos.length
          ? 'Marque para ver tudo o que a revista publicou, mesmo fora dos temas marcados. Sem a marca, só aparece o que combina com os temas.'
          : 'Você não marcou temas, então já aparece tudo. A marca vale quando você escolher temas.') + '</div>', '<a onclick="abrirConfig(false)">Editar</a>')
    : '';
  document.getElementById('sec-abelha').innerHTML = FILTROS.length ? facetaHtml(FILTROS[0]) : '';
  document.getElementById('so-conf').checked = soConf;

  // Revista
  const arrR = filtrar('rev'), contR = {};
  arrR.forEach(d => { if (d.revista) contR[d.revista] = (contR[d.revista] || 0) + 1; });
  const revs = Object.keys(contR).sort((a, b) => contR[b] - contR[a]);
  revistasSel.forEach(r => { if (!revs.includes(r)) revs.push(r); });
  const revsVis = revs.filter(r => !revBusca || r.toLowerCase().includes(revBusca) || revistasSel.includes(r)).slice(0, 300);
  document.getElementById('rev-list').innerHTML = revsVis.length
    ? checks(revsVis.map(r => ({ nome: r, n: contR[r] || 0, on: revistasSel.includes(r) })), 'rev')
    : '<div class="aviso-vazio">Nenhuma revista encontrada.</div>';

  // Mais filtros
  document.getElementById('btn-mais').textContent = maisAberto ? 'Menos filtros ▴' : 'Mais filtros ▾';
  let mais = '';
  if (maisAberto) {
    mais = FILTROS.slice(1).map(facetaHtml).join('') +
      (aba !== 'classico' ? '' : secao('Período', '<select onchange="setPeriodo(this.value)">' +
        [['', 'Qualquer ano'], ['5', 'Últimos 5 anos'], ['10', 'Últimos 10 anos'], ['2020+', '2020 em diante'],
         ['2010-2019', '2010 a 2019'], ['2000-2009', '2000 a 2009'], ['antes2000', 'Antes de 2000']]
          .map(p => '<option value="' + p[0] + '"' + (periodo === p[0] ? ' selected' : '') + '>' + p[1] + '</option>').join('') + '</select>')) +
      (TEM_SJR ? secao('Qualidade da revista (SJR)', '<select onchange="setQuartil(this.value)">' +
        [['', 'Qualquer'], ['com', 'Só com SJR (indexadas)'], ['Q1', 'Só Q1'], ['Q12', 'Q1 ou Q2'], ['Q123', 'Q1, Q2 ou Q3'], ['sem', 'Sem dado de SJR']]
          .map(p => '<option value="' + p[0] + '"' + (quartil === p[0] ? ' selected' : '') + '>' + p[1] + '</option>').join('') + '</select>') : '');
  }
  document.getElementById('mais-dyn').innerHTML = mais;
  const ativosF = !!(revistasSel.length || periodo || quartil || busca || soConf || Object.values(fac).some(s => s && s.length));
  document.getElementById('limpar-wrap').innerHTML = ativosF
    ? '<button class="btn perigo largo" style="margin-bottom:14px" onclick="limparFiltros()">Limpar filtros</button>' : '';
  document.getElementById('fnota').textContent = FILTROS.length
    ? 'As categorias são detectadas por palavras no título e no resumo e podem ter erros. Os números mostram quantos artigos sobram com os outros filtros aplicados.' : '';
  document.getElementById('ordem').value = ordem;

  // Lista
  const xs = ordenar(filtrar(''));
  document.getElementById('count').textContent = xs.length + ' artigo(s)' + (ativosF ? ' com os filtros escolhidos' : '');
  const parte = xs.slice(0, limite);
  let out = '', diaAtual = null;
  const porMes = !JANELAS[janelaIdx] || JANELAS[janelaIdx] > 30;
  for (const d of parte) {
    const ref = (d.data || d.adicionado || '').slice(0, porMes ? 7 : 10);
    if (aba === 'novo' && ordem === 'padrao' && ref !== diaAtual) {
      diaAtual = ref;
      out += '<h2 class="dia">' + (porMes ? esc(rotMes(ref)) : 'Publicados em ' + fmtData(ref)) + '</h2>';
    }
    out += itemHtml(d);
  }
  if (!parte.length) out = '<div class="vazio">Nada encontrado com esses filtros.</div>';
  document.getElementById('lista').innerHTML = out;
  document.getElementById('mais').style.display = xs.length > limite ? 'block' : 'none';
}

document.getElementById('sidebar').addEventListener('change', ev => {
  const i = ev.target;
  if (!i.matches || !i.matches('input[type=checkbox][data-tipo]')) return;
  const tp = i.dataset.tipo, o = i.dataset.o;
  limite = POR_PAGINA;
  if (tp === 'tema') { const t = CFG.topicos.find(x => x.id === o); if (t) { t.ativo = i.checked; salvarCfg(); } }
  else if (tp === 'conf') { const r = CFG.revistas[parseInt(o, 10)]; if (r) { r.mostrar = i.checked; salvarCfg(); } }
  else if (tp === 'rev') alternarSel(revistasSel, o);
  else if (tp === 'faceta') { const f = i.dataset.f; if (!fac[f]) fac[f] = []; alternarSel(fac[f], o); }
  render();
});
document.getElementById('lista').addEventListener('click', ev => {
  const b = ev.target.closest('button[data-acao]'); if (!b) return;
  const k = b.dataset.k, a = b.dataset.acao;
  if (a === 'quero' || a === 'lido') marcar(k, a); else if (a === 'zotero') enviarZotero(k); else if (a === 'motivo') abrirMotivo(k);
});

// ============================================================
//  Janela de configuração (abre sozinha na primeira visita)
// ============================================================
let TMP = null;
function revistaPadrao() { return (PADRAO.revistas || []).filter(r => r.padrao).map(r => ({ nome: r.nome, issns: r.issns.slice() })); }
function abrirConfig(inicial) {
  TMP = JSON.parse(JSON.stringify(CFG));
  if (inicial && !TMP.revistas.length) TMP.revistas = revistaPadrao();
  TMP._inicial = !!inicial;
  PROMPT_EDITADO = false;
  document.getElementById('modal-corpo').innerHTML = modalHtml(!!inicial);
  document.getElementById('modal').classList.add('on');
  FORM = { termos: [], editando: -1, cfg: null };
  desenharForm(); desenharTemas(); desenharRevistas();
}
function fecharConfig() {
  document.getElementById('modal').classList.remove('on');
  if (lsGet(K_CFG, null) === null) salvarCfg();   // não pergunta de novo a cada visita
  TMP = null;
}
function modalHtml(inicial) {
  return '<div class="modal-topo"><h2>' + (inicial ? 'Bem-vindo ao seu radar de abelhas' : 'Meus temas e revistas') + '</h2><p>' +
    (inicial ? 'Vamos configurar em dois minutos: você escolhe os <b>temas</b> que quer acompanhar e as <b>revistas de confiança</b>. Tudo fica salvo neste navegador e dá para mudar quando quiser.'
             : 'Mude seus temas, suas revistas de confiança e as conexões. As escolhas ficam salvas neste navegador.') + '</p></div>' +
    '<section><h3>1. Seus temas</h3><p class="dica">Um tema é um assunto que você quer acompanhar. Dê um <b>título</b> e escreva as <b>palavras-chave</b> que o definem, em inglês (é como os artigos são escritos). Um artigo entra no tema se tiver <b>qualquer uma</b> das palavras no título ou no resumo. Sem nenhum tema, o site mostra todos os artigos.</p>' +
    '<div class="form-tema" id="form-tema"><h4 id="ft-cab">Novo tema</h4>' +
    '<div class="campo"><label for="ft-titulo">Título do tema</label><input type="text" id="ft-titulo" placeholder="Ex.: Socialidade" oninput="desenharIdeias();atualizarPrompt()" onkeydown="if(event.key===\'Enter\'){event.preventDefault();document.getElementById(\'ft-palavra\').focus();}"></div>' +
    '<div class="campo"><label for="ft-palavra">Palavras-chave</label><div class="chip-input" onclick="document.getElementById(\'ft-palavra\').focus()"><span id="ft-chips" style="display:contents"></span>' +
    '<input type="text" id="ft-palavra" autocomplete="off" placeholder="Digite uma palavra e tecle Enter (ex.: eusociality)" oninput="palavraInput(this)" onpaste="setTimeout(() => { palavraInput(this); flushPalavra(); }, 0)" onkeydown="palavraTecla(event,this)"></div>' +
    '<div class="ajuda">Tecle <b>Enter</b> ou digite uma <b>vírgula</b> para adicionar cada palavra. Frases também valem, como <i>division of labor</i>.</div>' +
    '<div class="err-msg" id="ft-aviso" style="font-size:12px;margin-top:4px"></div></div>' +
    '<div class="acoes-form"><button class="btn forte" id="ft-salvar" onclick="salvarTema()">Adicionar tema</button><button class="btn" id="ft-cancelar" style="display:none" onclick="limparForm()">Cancelar edição</button><span id="ft-msg" class="err-msg"></span></div>' +
    '<div class="previa" id="ft-previa"></div><div class="ideias" id="ft-ideias"></div>' +
    '<details class="guia"><summary>Como escolher boas palavras-chave? (com prompt para IA)</summary><ol>' +
    '<li><b>Pense em inglês.</b> Os artigos são escritos em inglês: <i>socialidade</i> vira <i>eusociality</i>, <i>social behavior</i>…</li>' +
    '<li><b>Comece pelo conceito central e acrescente sinônimos</b> (eusocial, eusociality, social behavior). Quanto mais jeitos de dizer a mesma coisa, menos artigos escapam.</li>' +
    '<li><b>Misture termos gerais e específicos</b> (<i>caste</i>, <i>division of labor</i>, <i>queen-worker conflict</i>). Evite palavras genéricas sozinhas, como <i>behavior</i>, <i>study</i> ou <i>species</i>: elas trazem de tudo.</li>' +
    '<li><b>Plural não precisa:</b> <i>nest</i> já pega <i>nests</i>. Mas escreva as duas grafias quando existirem (<i>behavior</i> e <i>behaviour</i>).</li>' +
    '<li><b>Use frases entre aspas mentais:</b> <i>heat stress</i> é bem melhor que <i>heat</i> e <i>stress</i> separados.</li>' +
    '<li><b>Gêneros e espécies funcionam</b> (<i>Melipona</i>, <i>Bombus</i>, <i>Osmia bicornis</i>).</li>' +
    '<li><b>Olhe o contador:</b> a etiqueta da palavra mostra quantos artigos carregados a usam. Zero = palavra rara ou erro de digitação; centenas = ampla demais.</li>' +
    '<li><b>Revise depois de alguns dias:</b> veja o que entrou e ajuste (Editar).</li></ol>' +
    '<div class="prompt-ia"><div style="font-weight:700;margin-bottom:2px">Peça ajuda a uma IA (ChatGPT, Claude, Gemini…)</div>' +
    '<p class="ajuda" style="margin:2px 0 6px">1) Copie o prompt abaixo: ele já leva o título e as palavras que você escreveu. 2) Cole na IA que você usa. 3) Cole a resposta no campo de palavras-chave: cada palavra vira uma etiqueta. 4) Confira os contadores e apague o que não servir. A IA pode errar ou inventar termos.</p>' +
    '<textarea id="ft-prompt" rows="14" oninput="PROMPT_EDITADO=true" aria-label="Prompt para copiar"></textarea>' +
    '<div class="acoes-form"><button class="btn forte mini" onclick="copiarPrompt()">Copiar prompt</button><button class="btn mini" onclick="restaurarPrompt()">Restaurar texto</button></div></div></details>' +
    '</div>' +
    '<div class="sug-titulo">Seus temas</div><div id="cfg-temas" style="margin-top:8px"></div>' +
    '</section>' +
    '<section><h3>2. Revistas de confiança</h3><p class="dica">São as revistas em que você confia. Na barra lateral, você <b>marca</b> uma delas quando quiser ver <b>tudo o que ela publicou</b>, mesmo fora dos seus temas; sem a marca, valem só os temas escolhidos. Escreva o nome ou o ISSN.</p>' +
    '<div class="entrada"><input type="text" id="cfg-rev" placeholder="Ex.: Apidologie ou 0044-8435" onkeydown="if(event.key===\'Enter\'){procurarRevista();event.preventDefault();}"><button class="btn forte" onclick="procurarRevista()">Procurar</button></div>' +
    '<div class="achados" id="cfg-rev-res"></div><div class="chips" id="cfg-revs"></div><div class="sug-titulo">Sugestões</div><div class="chips" id="cfg-sug-revs"></div></section>' +
    '<section><h3>3. Conexões <span style="font-weight:400;font-size:13px;color:var(--mut)">(opcional)</span></h3>' +
    '<div class="campo"><label for="cfg-oakey">Chave gratuita do OpenAlex</label><input type="password" id="cfg-oakey" autocomplete="off" value="' + esc(TMP.openalexKey || '') + '" placeholder="Cole aqui a sua chave">' +
    '<div class="ajuda">Usada para buscar as revistas de confiança. Crie uma de graça em openalex.org (Configurações &gt; API). Sem chave também funciona, com limite menor.</div></div>' +
    '<div class="campo"><label for="cfg-zkey">Chave da API do Zotero</label><div class="entrada" style="margin-bottom:4px"><input type="password" id="cfg-zkey" autocomplete="off" value="' + esc(TMP.zotero.key || '') + '" placeholder="Cole a chave com permissão de escrita"><button class="btn" onclick="conectarZotero()">Conectar</button></div>' +
    '<div id="cfg-zmsg" class="' + (TMP.zotero.user ? 'ok-msg' : 'ajuda') + '">' + (TMP.zotero.user ? 'Conectado (usuário ' + esc(TMP.zotero.user) + ').' : '') + '</div>' +
    '<div class="ajuda">Crie em zotero.org/settings/keys marcando "Allow library access" e "Allow write access". O ID da biblioteca é descoberto sozinho.</div></div>' +
    '<div class="campo"><label for="cfg-zcol">Pasta principal no Zotero</label><input type="text" id="cfg-zcol" value="' + esc(TMP.zotero.colecao || COLECAO_PADRAO) + '">' +
    '<div class="ajuda">O botão "Quero ler" cria a subpasta "Quero ler" dentro dela, e "Lido" cria a subpasta "Lido".</div></div></section>' +
    '<div class="modal-rodape"><button class="btn" onclick="fecharConfig()">' + (inicial ? 'Pular por enquanto' : 'Cancelar') + '</button><button class="btn forte" onclick="concluirConfig()">Salvar e ' + (inicial ? 'começar' : 'aplicar') + '</button></div>';
}
let FORM = { termos: [], editando: -1, cfg: null };
function limparForm() {
  FORM = { termos: [], editando: -1, cfg: null };
  const t = document.getElementById('ft-titulo'), p = document.getElementById('ft-palavra');
  if (t) t.value = ''; if (p) p.value = '';
  desenharForm(); desenharTemas();
}
const GENERICAS = ['bee', 'bees', 'behavior', 'behaviour', 'study', 'studies', 'effect', 'effects', 'species', 'insect', 'insects', 'analysis', 'research', 'review', 'model', 'data', 'result', 'results'];
let _UNICOS = null, _UNICOS_N = -1;
function unicos() {
  if (_UNICOS && _UNICOS_N === ITENS.length) return _UNICOS;
  const m = {}; ITENS.forEach(d => { if (!m[d.key]) { d._tt = ((d.titulo || '') + ' ' + (d.resumo || '')).toLowerCase(); m[d.key] = d; } });
  _UNICOS = Object.values(m); _UNICOS_N = ITENS.length; _DF_ALL = null; return _UNICOS;
}
function casaPalavra(d, p) { return reTermo(p).test(d._tt || (d._tt = ((d.titulo || '') + ' ' + (d.resumo || '')).toLowerCase())); }
function desenharChipsPalavras() {
  const el = document.getElementById('ft-chips'); if (!el) return;
  const base = unicos();
  el.innerHTML = FORM.termos.map((p, i) => {
    const n = base.filter(d => casaPalavra(d, p)).length, gen = GENERICAS.includes(p.toLowerCase());
    const dica = gen ? 'Palavra muito genérica: pode trazer artigos fora do tema.' : n === 0 ? 'Nenhum artigo carregado usa esta palavra (palavra rara ou erro de digitação?).' : n + ' artigo(s) carregado(s) usam esta palavra.';
    return '<span class="chip' + (n === 0 ? ' zero' : '') + (gen ? ' generica' : '') + '" title="' + esc(dica) + '">' + esc(p) + ' <span class="cnt">' + n + '</span><button class="x" title="Remover esta palavra" onclick="removerPalavra(' + i + ')">×</button></span>';
  }).join('');
  const av = document.getElementById('ft-aviso'), g = FORM.termos.filter(p => GENERICAS.includes(p.toLowerCase()));
  if (av) av.textContent = g.length ? 'A palavra "' + g[0] + '" é muito genérica e pode trazer artigos fora do tema. Prefira frases mais específicas.' : '';
  atualizarPrevia(); desenharIdeias(); atualizarPrompt();
}
function atualizarPrevia() {
  const el = document.getElementById('ft-previa'); if (!el) return;
  if (!FORM.termos.length) { el.innerHTML = 'Adicione palavras-chave para ver quantos artigos carregados combinam com o tema.'; return; }
  const base = unicos(), hit = base.filter(d => FORM.termos.some(p => casaPalavra(d, p)));
  el.innerHTML = 'Prévia: <b>' + hit.length + '</b> de ' + base.length + ' artigos carregados (últimos dias + clássicos) combinam com estas palavras.' +
    (hit.length ? '<ul>' + hit.slice(0, 3).map(d => '<li>' + esc(d.titulo) + '</li>').join('') + '</ul>' : (base.length ? ' Tente sinônimos ou palavras mais gerais.' : ''));
}
// ---- ideias de palavras ----
const STOP = new Set(('a about above after again against all also although among an and any are as at be because been before being between both but by can could did do does during each either else for from further had has have having here how however if in into is it its just may might more most much must no nor not of on once only or other our out over own per same should since so some such than that the their them then there these they this those through thus to too under until up upon use used using very was we were what when where which while who whom why will with within without would yet via et al').split(' '));
const GENERICAS_TXT = new Set(('study studies result results show shows showed shown found find finding findings based suggest suggests suggested analysis analyses data effect effects high higher low lower increase increased decrease decreased new large small different similar important potential however mainly present presented provide provides provided research paper article review compared comparison across approach number total overall significant significantly respectively associated levels level rate rates years year time one two three first second known species bee bees insect insects').split(' '));
let _DF_ALL = null;
function tokensDe(t) { return (String(t).toLowerCase().match(/[a-z][a-z-]{3,}/g) || []).filter(w => !STOP.has(w) && !GENERICAS_TXT.has(w)); }
function raiz(w) { return w.length > 4 ? w.replace(/ies$/, 'y').replace(/sses$/, 'ss').replace(/s$/, '') : w; }
function termosDoc(d) {
  const tk = tokensDe(d._tt || ''), out = new Set();
  tk.forEach((w, i) => { out.add(raiz(w)); });
  const bruto = String(d._tt || '').toLowerCase().match(/[a-z][a-z-]*/g) || [];
  const bom = w => w.length >= 4 && !STOP.has(w) && !GENERICAS_TXT.has(w);
  for (let i = 0; i + 1 < bruto.length; i++) { const a = bruto[i], b = bruto[i + 1]; if (bom(a) && bom(b)) out.add(raiz(a) + ' ' + raiz(b)); }
  return out;
}
function dfTodos() {
  if (_DF_ALL) return _DF_ALL;
  const df = {}; unicos().forEach(d => termosDoc(d).forEach(t => { df[t] = (df[t] || 0) + 1; }));
  _DF_ALL = df; return df;
}
function ideiasCoocorrencia(max) {
  const base = unicos(), N = base.length;
  if (!FORM.termos.length || N < 8) return [];
  const alvo = base.filter(d => FORM.termos.some(p => casaPalavra(d, p)));
  if (alvo.length < 3) return [];
  const dfA = {}, forma = {}, dfT = dfTodos();
  alvo.forEach(d => { termosDoc(d).forEach(t => { dfA[t] = (dfA[t] || 0) + 1; }); });
  const jaTem = new Set(FORM.termos.map(p => raiz(p.toLowerCase())).concat(FORM.termos.map(p => p.toLowerCase())));
  let cand = Object.keys(dfA).filter(t => dfA[t] >= 2 && dfA[t] / alvo.length >= (t.includes(' ') ? 0.2 : 0.12) && !jaTem.has(t)
      && !FORM.termos.some(p => p.toLowerCase().includes(t)));
  // uma frase que aparece nos mesmos artigos que uma de suas palavras ganha da palavra solta (mais específica)
  const sobra = new Set(cand);
  cand.filter(t => t.includes(' ')).forEach(b => b.split(' ').forEach(c => { if (dfA[c] === dfA[b]) sobra.delete(c); }));
  cand = cand.filter(t => sobra.has(t));
  return cand.map(t => ({ termo: t, n: dfA[t], pts: dfA[t] * Math.log((N + 1) / (dfT[t] || 1)) * (t.includes(' ') ? 1.15 : 1) }))
    .sort((a, b) => b.pts - a.pts).slice(0, max || 10);
}
function ideiasVocabulario() {
  const tit = norm(valor('ft-titulo')), usados = FORM.termos.map(p => p.toLowerCase());
  const achou = [];
  (PADRAO.vocabulario || []).forEach(v => {
    const nomes = [v.conceito].concat(v.aliases || []).map(norm).filter(Boolean);
    const portitulo = tit && nomes.some(n => (' ' + tit + ' ').includes(' ' + n + ' ') || tit === n);
    const porpalavra = (v.palavras || []).some(p => usados.includes(p.toLowerCase()));
    if (portitulo || porpalavra) achou.push({ v, ord: portitulo ? 0 : 1 });
  });
  return achou.sort((a, b) => a.ord - b.ord).slice(0, 3).map(x => ({ conceito: x.v.conceito, palavras: x.v.palavras.filter(p => !usados.includes(p.toLowerCase())), titulo: x.ord === 0 }))
    .filter(x => x.palavras.length);
}
let IDEIAS_OA = null;
function chipIdeia(p, n) { return '<span class="chip sug" onclick="usarIdeia(this.dataset.p)" data-p="' + esc(p) + '">＋ ' + esc(p) + (n ? ' <span class="cnt">' + n + '</span>' : '') + '</span>'; }
function desenharIdeias() {
  const el = document.getElementById('ft-ideias'); if (!el) return;
  let h = '';
  ideiasVocabulario().forEach(g => { h += '<div class="grupo"><div class="rot2">' + (g.titulo ? 'Ideias para "' + esc(g.conceito) + '"' : 'Ideias parecidas: ' + esc(g.conceito)) + ' (clique para adicionar)</div><div class="chips">' + g.palavras.map(p => chipIdeia(p)).join('') + '</div></div>'; });
  const jaMostradas = new Set(ideiasVocabulario().flatMap(g => g.palavras.map(p => p.toLowerCase())));
  const frasesMostradas = [...jaMostradas].filter(p => p.includes(' '));
  const co = ideiasCoocorrencia(16).filter(x => !jaMostradas.has(x.termo) && !frasesMostradas.some(p => p.split(/\s+/).includes(x.termo))).slice(0, 10);
  if (co.length) h += '<div class="grupo"><div class="rot2">Palavras que aparecem junto nos artigos carregados (o número é quantos artigos)</div><div class="chips">' + co.map(x => chipIdeia(x.termo, x.n)).join('') + '</div></div>';
  if (IDEIAS_OA) {
    if (IDEIAS_OA.erro) h += '<div class="err-msg" style="font-size:12px">' + esc(IDEIAS_OA.erro) + '</div>';
    else IDEIAS_OA.topicos.forEach(t => { const ps = t.keywords.filter(p => !FORM.termos.some(x => x.toLowerCase() === p.toLowerCase())); if (ps.length) h += '<div class="grupo"><div class="rot2">Do OpenAlex, assunto "' + esc(t.nome) + '"</div><div class="chips">' + ps.map(p => chipIdeia(p)).join('') + '</div></div>'; });
  }
  if (FORM.termos.length || valor('ft-titulo')) h += '<button class="btn mini" id="ft-oa" onclick="ideiasOpenAlex()">Buscar mais ideias no OpenAlex</button>';
  el.innerHTML = h;
}
function usarIdeia(p) { addPalavra(p); desenharChipsPalavras(); const i = document.getElementById('ft-palavra'); if (i) i.focus(); }
async function ideiasOpenAlex() {
  const q = FORM.termos[0] || valor('ft-titulo'); if (!q) return;
  const b = document.getElementById('ft-oa'); if (b) { b.disabled = true; b.textContent = 'Buscando…'; }
  try {
    const j = await oaGet('/topics', { search: q, 'per-page': 3 }, valor('cfg-oakey') || (TMP && TMP.openalexKey) || '');
    const ts = (j.results || []).map(t => ({ nome: t.display_name, keywords: (t.keywords || []).filter(Boolean) })).filter(t => t.keywords.length);
    IDEIAS_OA = ts.length ? { topicos: ts } : { erro: 'O OpenAlex não achou assuntos para "' + q + '". Tente uma palavra em inglês.' };
  } catch (e) { IDEIAS_OA = { erro: 'Não consegui buscar no OpenAlex: ' + (e.message || e) }; }
  desenharIdeias();
}
function desenharForm() {
  if (!document.getElementById('form-tema')) return;
  const ed = FORM.editando >= 0;
  desenharChipsPalavras();
  document.getElementById('ft-cab').textContent = ed ? 'Editando o tema "' + (TMP.topicos[FORM.editando] || {}).nome + '"' : 'Novo tema';
  IDEIAS_OA = null;
  document.getElementById('ft-salvar').textContent = ed ? 'Salvar alterações' : 'Adicionar tema';
  document.getElementById('ft-cancelar').style.display = ed ? 'inline-block' : 'none';
  document.getElementById('form-tema').classList.toggle('editando', ed);
  document.getElementById('ft-msg').textContent = '';
}
let PROMPT_EDITADO = false;
function montarPrompt() {
  const titulo = valor('ft-titulo'), tem = FORM.termos;
  return [
    'Você é um especialista em abelhas (ecologia, comportamento e taxonomia) e em busca bibliográfica.',
    'Preciso de palavras-chave em INGLÊS para filtrar artigos científicos novos sobre abelhas.',
    '',
    'TEMA: ' + (titulo || '[ESCREVA AQUI O NOME DO TEMA, por exemplo: Socialidade]'),
    '[SE QUISER, DESCREVA AQUI EM UMA OU DUAS FRASES O QUE VOCÊ QUER ACOMPANHAR NESSE TEMA]',
    tem.length ? 'PALAVRAS QUE EU JÁ TENHO (não repita): ' + tem.join(', ') : null,
    '',
    'COMO O FILTRO FUNCIONA: ele procura cada palavra ou frase no TÍTULO e no RESUMO dos artigos, e o artigo entra se tiver QUALQUER uma delas. Plurais simples são tratados sozinhos (nest = nests), mas sinônimos e grafias diferentes (behavior/behaviour) não.',
    '',
    'O QUE EU QUERO:',
    '1. Entre 15 e 30 palavras-chave ou frases curtas em inglês, do jeito que os pesquisadores escrevem em títulos e resumos.',
    '2. Misture termos gerais do tema, termos específicos e sinônimos. Inclua variações de grafia (britânica e americana) e, quando fizer sentido, nomes de gêneros ou grupos de abelhas.',
    '3. Prefira frases de 2 a 3 palavras a palavras soltas. Evite termos genéricos demais ("behavior", "study", "species", "bee"), que trariam artigos de outros assuntos.',
    '4. Não numere, não explique e não use aspas.',
    '',
    'FORMATO DA RESPOSTA: somente as palavras e frases separadas por vírgula, em uma única linha, para eu copiar e colar.'
  ].filter(l => l !== null).join('\n');
}
function atualizarPrompt() { const ta = document.getElementById('ft-prompt'); if (ta && !PROMPT_EDITADO) ta.value = montarPrompt(); }
function restaurarPrompt() { PROMPT_EDITADO = false; atualizarPrompt(); }
async function copiarPrompt() {
  const ta = document.getElementById('ft-prompt'); if (!ta) return;
  const aviso = () => toast('Prompt copiado! Cole na sua IA e depois cole a resposta no campo de palavras-chave.');
  try {
    if (navigator.clipboard && navigator.clipboard.writeText) { await navigator.clipboard.writeText(ta.value); aviso(); return; }
    ta.select(); if (document.execCommand('copy')) { aviso(); return; }
    throw new Error('sem acesso à área de transferência');
  } catch (e) { ta.select(); toast('Não consegui copiar sozinho: o texto está selecionado, use Ctrl+C.', true); }
}
function addPalavra(p) {
  p = String(p || '').trim().replace(/^(\d+[.)]|[-•*])\s+/, '').replace(/^["'“”‘’(\[]+|["'“”‘’)\]]+$/g, '').replace(/\.+$/, '').replace(/\s+/g, ' ').trim();
  if (p && !FORM.termos.some(x => x.toLowerCase() === p.toLowerCase())) FORM.termos.push(p);
}
function palavraInput(el) {   // vírgula, ponto e vírgula ou quebra de linha (ao colar uma lista) viram etiquetas
  if (/[,;\n]/.test(el.value)) { const partes = el.value.split(/[,;\n]/); el.value = partes.pop(); partes.forEach(addPalavra); desenharChipsPalavras(); }
}
function palavraTecla(ev, el) {
  if (ev.key === 'Enter') { ev.preventDefault(); addPalavra(el.value); el.value = ''; desenharChipsPalavras(); }
  else if (ev.key === 'Backspace' && !el.value && FORM.termos.length) { FORM.termos.pop(); desenharChipsPalavras(); }
}
function flushPalavra() { const el = document.getElementById('ft-palavra'); if (el && el.value.trim()) { addPalavra(el.value); el.value = ''; desenharChipsPalavras(); } }
function removerPalavra(i) { FORM.termos.splice(i, 1); desenharChipsPalavras(); }
function cfgAindaValido(nomeCfg, termos) {   // se o usuário mexeu nas palavras de um modelo, deixa de usar as etiquetas prontas do robô
  const m = (PADRAO.topicos || []).find(t => t.nome === nomeCfg); if (!m) return null;
  const a = new Set(termos.map(x => norm(x))), b = new Set(m.termos.map(x => norm(x)));
  return a.size === b.size && [...a].every(x => b.has(x)) ? nomeCfg : null;
}
function salvarTema() {
  flushPalavra();
  const nome = valor('ft-titulo').replace(/\s+/g, ' '), msg = document.getElementById('ft-msg');
  const erro = t => { msg.textContent = t; return false; };
  if (!nome) return erro('Dê um título ao tema.');
  if (!FORM.termos.length) return erro('Escreva pelo menos uma palavra-chave.');
  if (TMP.topicos.some((t, i) => i !== FORM.editando && norm(t.nome) === norm(nome))) return erro('Já existe um tema com esse título.');
  const cfgNome = cfgAindaValido(FORM.cfg, FORM.termos);
  if (FORM.editando >= 0) { const t = TMP.topicos[FORM.editando]; t.nome = nome; t.termos = FORM.termos.slice(); t.cfg = cfgNome; }
  else TMP.topicos.push({ id: novoId(), nome, termos: FORM.termos.slice(), ativo: true, cfg: cfgNome });
  limparForm();
  return true;
}
function editarTema(i) {
  const t = TMP.topicos[i]; if (!t) return;
  FORM = { termos: (t.termos || []).slice(), editando: i, cfg: t.cfg || null };
  document.getElementById('ft-titulo').value = t.nome;
  desenharForm(); desenharTemas();
  const f = document.getElementById('form-tema'); if (f.scrollIntoView) f.scrollIntoView({ behavior: 'smooth', block: 'center' });
}
function removerTema(i) { TMP.topicos.splice(i, 1); if (FORM.editando === i) { limparForm(); return; } if (FORM.editando > i) FORM.editando--; desenharTemas(); }
function desenharTemas() {
  const el = document.getElementById('cfg-temas');
  if (!el) return;
  el.innerHTML = TMP.topicos.length
    ? TMP.topicos.map((t, i) => '<div class="tema-card' + (i === FORM.editando ? ' editando' : '') + '"><div class="tema-info"><b>' + esc(t.nome) + '</b>' +
        '<div class="tema-termos">' + esc((t.termos || []).join(' · ')) + '</div></div><div class="tema-acoes">' +
        '<button class="btn mini" onclick="editarTema(' + i + ')">Editar</button><button class="btn mini perigo" onclick="removerTema(' + i + ')">Remover</button></div></div>').join('')
    : '<div class="dica" style="margin:0 0 10px">Você ainda não criou nenhum tema.</div>';
}

function desenharRevistas() {
  const el = document.getElementById('cfg-revs'), sg = document.getElementById('cfg-sug-revs');
  if (!el) return;
  el.innerHTML = TMP.revistas.length
    ? TMP.revistas.map((r, i) => '<span class="chip" title="ISSN ' + esc((r.issns || []).join(', ')) + '">' + esc(r.nome) + '<button class="x" title="Remover" onclick="removerRevista(' + i + ')">×</button></span>').join('')
    : '<span class="dica" style="margin:0">Nenhuma revista de confiança ainda.</span>';
  const tem = new Set(TMP.revistas.map(r => norm(r.nome)));
  const sug = (PADRAO.revistas || []).map((r, i) => ({ r, i })).filter(x => !tem.has(norm(x.r.nome)));
  sg.innerHTML = sug.length ? sug.map(x => '<span class="chip sug" onclick="addSugRevista(' + x.i + ')">＋ ' + esc(x.r.nome) + '</span>').join('')
    : '<span class="dica" style="margin:0">Sem outras sugestões.</span>';
}
function addSugRevista(i) { const s = PADRAO.revistas[i]; if (s) { TMP.revistas.push({ nome: s.nome, issns: s.issns.slice() }); desenharRevistas(); } }
function removerRevista(i) { TMP.revistas.splice(i, 1); desenharRevistas(); }
let ACHADOS = [];
async function procurarRevista() {
  const q = valor('cfg-rev'), alvo = document.getElementById('cfg-rev-res'); if (!q) return;
  alvo.innerHTML = '<div class="dica">Procurando…</div>';
  const chave = valor('cfg-oakey') || TMP.openalexKey || '';
  try {
    let lista;
    if (/^\d{4}-?\d{3}[\dXx]$/.test(q)) {
      const issn = q.includes('-') ? q : q.slice(0, 4) + '-' + q.slice(4), s = await oaGet('/sources/issn:' + issn, {}, chave);
      lista = s && s.id ? [s] : [];
    } else { lista = (await oaGet('/sources', { search: q, 'per-page': 6 }, chave)).results || []; }
    ACHADOS = lista;
    alvo.innerHTML = lista.length ? lista.map((s, i) => '<div class="achado"><div>' + esc(s.display_name) +
      '<small>' + esc([s.issn_l, s.host_organization_name, s.works_count ? s.works_count.toLocaleString('pt-BR') + ' trabalhos' : ''].filter(Boolean).join(' · ')) + '</small></div>' +
      '<button class="btn mini forte" onclick="addAchada(' + i + ')">Adicionar</button></div>').join('')
      : '<div class="err-msg">Não encontrei essa revista. Tente o ISSN.</div>';
  } catch (e) { alvo.innerHTML = '<div class="err-msg">' + esc(e.message || 'Erro na busca') + '</div>'; }
}
function addAchada(i) {
  const s = ACHADOS[i]; if (!s) return;
  const issns = [].concat(s.issn_l ? [s.issn_l] : [], s.issn || []).filter((v, k, a) => a.indexOf(v) === k);
  if (!TMP.revistas.some(r => norm(r.nome) === norm(s.display_name))) TMP.revistas.push({ nome: s.display_name, issns });
  document.getElementById('cfg-rev-res').innerHTML = ''; document.getElementById('cfg-rev').value = ''; desenharRevistas();
}
async function conectarZotero(silencioso) {
  const k = valor('cfg-zkey'), msg = document.getElementById('cfg-zmsg');
  if (!k) { if (msg) { msg.className = 'err-msg'; msg.textContent = 'Cole a chave primeiro.'; } return false; }
  if (msg) { msg.className = 'ajuda'; msg.textContent = 'Conectando…'; }
  try {
    const r = await fetch(ZOT + '/keys/current', { headers: { 'Zotero-API-Key': k, 'Zotero-API-Version': '3' } });
    if (!r.ok) throw new Error(r.status === 403 || r.status === 404 ? 'chave inválida' : 'erro ' + r.status);
    const j = await r.json(), escrita = !!(((j.access || {}).user || {}).write);
    TMP.zotero.key = k; TMP.zotero.user = String(j.userID);
    if (msg) { msg.className = escrita ? 'ok-msg' : 'err-msg';
      msg.textContent = escrita ? 'Conectado como ' + (j.username || j.userID) + '.' : 'Conectado, mas esta chave NÃO tem permissão de escrita. Crie outra marcando "Allow write access".'; }
    return escrita;
  } catch (e) { if (msg) { msg.className = 'err-msg'; msg.textContent = 'Não consegui conectar: ' + (e.message || e); } return false; }
}
async function concluirConfig() {
  flushPalavra();
  if (valor('ft-titulo') && FORM.termos.length) salvarTema();   // não perde um tema que ficou escrito e sem clicar em Adicionar
  TMP.openalexKey = valor('cfg-oakey');
  const novaChave = valor('cfg-zkey');
  if (novaChave !== TMP.zotero.key) { TMP.zotero.key = novaChave; TMP.zotero.user = ''; }
  if (TMP.zotero.key && !TMP.zotero.user) await conectarZotero(true);
  if (!TMP.zotero.key) TMP.zotero.user = '';
  TMP.zotero.colecao = valor('cfg-zcol') || COLECAO_PADRAO;
  TMP.topicos.forEach(t => { if (!t.id) t.id = novoId(); if (t.ativo === undefined) t.ativo = true; });
  const mudouRev = JSON.stringify(TMP.revistas) !== JSON.stringify(CFG.revistas), eraPrimeira = !!TMP._inicial;
  delete TMP._inicial;
  CFG = TMP; salvarCfg(); TMP = null;
  document.getElementById('modal').classList.remove('on');
  montarItens(); render();
  if (mudouRev || eraPrimeira) atualizarConfiaveisSeguro(true);
}

renderHero();
montarItens();
render();
if (PRIMEIRA_VEZ) abrirConfig(true); else atualizarConfiaveisSeguro(false);
</script>
</body>
</html>
"""


def gerar_site(cfg, state, hoje):
    escopo = carregar_scopus(cfg)
    hist = historico_dias(cfg)
    livre = modo_busca(cfg) == "revistas"   # a lista de revistas já decidiu o que entra
    itens = [d for d in state.get("arquivo", [])
             if (livre or d.get("completa")
                 or (revista_ok(d.get("revista"), cfg) and not excluida(d, cfg) and scopus_ok(d, escopo)))
             and na_janela(d, hoje, hist)]
    for nome, fila in state.get("fila_classicos", {}).items():
        for r in fila:
            if livre or (revista_ok(r.get("revista"), cfg) and not excluida(r, cfg) and scopus_ok(r, escopo)):
                itens.append(para_site(r, nome, "classico", ""))
    comp = compilar_facetas(cfg)
    for d in itens:
        if not d.get("facetas"):
            d["facetas"] = classificar(d.get("titulo"), d.get("resumo"), comp)
    por_issn, por_titulo = carregar_sjr(cfg)
    saida = []
    for d in itens:
        x = {k: v for k, v in d.items() if k != "issn" or d.get("completa")}
        hit = sjr_de(d, por_issn, por_titulo)
        x["sjr"], x["q"] = (hit[0], hit[1]) if hit else (None, "")
        saida.append(x)
    dados = json.dumps(saida, ensure_ascii=False).replace("</", "<\\/")
    filtros_json = json.dumps(definicao_filtros_js(cfg), ensure_ascii=False).replace("</", "<\\/")
    try:
        fotos = fotos_das_especies(cfg, state, hoje)
    except Exception as e:
        log(f"⚠ Fotos indisponíveis: {e}")
        fotos = []
    padrao_json = json.dumps(padrao_para_site(cfg, state), ensure_ascii=False).replace("</", "<\\/")
    fotos_json = json.dumps(fotos, ensure_ascii=False).replace("</", "<\\/")
    site = cfg.get("site", {})
    pagina = (SITE_TEMPLATE
              .replace("__TITULO__", html.escape(site.get("titulo", "Radar de artigos")))
              .replace("__SUBTITULO__", html.escape(site.get("subtitulo", "")))
              .replace("__ATUALIZADO__", hoje.strftime("%d/%m/%Y"))
              .replace("__FILTROS_DEF__", filtros_json)
              .replace("__PADRAO__", padrao_json)
              .replace("__FOTOS__", fotos_json)
              .replace("__FOTO_MODO__", json.dumps(modo_foto(cfg)))
              .replace("__FOTO_ALTURA__", str(altura_foto(cfg)))
              .replace("__NOVDIAS__", str(novidades_dias(cfg)))
              .replace("__JANELAS__", json.dumps(janelas_site(cfg)))
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
    escopo = carregar_scopus(cfg)
    h = json.dumps([cfg.get("filtro_revistas"), cfg.get("excluir"), c, cfg["topicos"],
                    cfg.get("filtros"), cfg.get("scopus"), escopo["assinatura"] if escopo else None,
                    modo_busca(cfg), cfg.get("revistas")],
                   sort_keys=True, default=str, ensure_ascii=False)
    if state.get("classicos_hash") != h:
        state["fila_classicos"] = {}      # filtro mudou: refaz a lista
        state["classicos_hash"] = h
    fila = state.setdefault("fila_classicos", {})
    comp = compilar_facetas(cfg)
    filtro_on = bool((cfg.get("filtro_revistas") or {}).get("ativo")) or bool(
        (cfg.get("excluir") or {}).get("termos")) or escopo is not None
    por_pagina = 100 if filtro_on else min(100, c["por_topico"])
    revistas_modo = modo_busca(cfg) == "revistas"
    ids_rev = [i["id"] for e, i in resolver_todas(cfg, state)] if revistas_modo else []
    for t in cfg["topicos"]:
        if t["nome"] in fila:
            continue
        try:
            if revistas_modo:   # os clássicos também vêm só das revistas escolhidas
                recs = []
                for k in range(0, len(ids_rev), 50):
                    recs += openalex_search(t, sort="cited_by_count:desc", per_page=100, ate_ano=c.get("ate_ano"),
                                            extra_filtros=["primary_location.source.id:" + "|".join(ids_rev[k:k + 50])])
                recs = dedup(sorted(recs, key=lambda r: -(r.get("citacoes") or 0)))[: c["por_topico"]]
            else:
                recs = openalex_search(t, sort="cited_by_count:desc", per_page=por_pagina,
                                       paginas=2 if filtro_on else 1, ate_ano=c.get("ate_ano"))
                recs = [r for r in recs
                        if revista_ok(r["revista"], cfg) and not excluida(r, cfg)
                        and scopus_ok(r, escopo)][: c["por_topico"]]
            for r in recs:
                r["facetas"] = classificar(r["titulo"], r.get("resumo"), comp)
                r["motivo"] = motivo_classico(r, t)
            fila[t["nome"]] = [leve(r) for r in recs]
            log(f"Clássicos carregados: {t['nome']} ({len(recs)})")
        except Exception as e:
            log(f"Erro ao buscar clássicos de {t['nome']}: {e}")


def run_diario(cfg, state, dias, enviar):
    aviso_chave()
    hoje = date.today()
    b = cfg["busca"]
    nomes = sorted(t["nome"] for t in cfg["topicos"])
    modo = modo_busca(cfg)
    amplo = modo == "amplo"
    revistas_modo = modo == "revistas"
    etiquetar = modo in ("amplo", "revistas")   # nesses modos os temas são etiquetas, não filtros
    if state.get("modo_busca") != modo:
        log(f"Modo de busca agora é '{modo}': reiniciando o arquivo do site.")
        state["arquivo"], state["vistos"], state["historico_feito"] = [], [], 0
        state["modo_busca"] = modo
        state["nomes_topicos"] = nomes
    if modo == "por_tema" and state.get("nomes_topicos") != nomes:
        log("Lista de tópicos mudou: reiniciando o arquivo do site.")
        state["arquivo"], state["vistos"] = [], []
        state["nomes_topicos"] = nomes
    comp_temas = compilar_temas(cfg)
    th = hash_temas(cfg)
    if etiquetar and state.get("temas_hash") != th:   # temas mudaram: reetiqueta o que já está no site
        for d in state.get("arquivo", []):
            d["temas"] = classificar_temas(d, comp_temas)
            d["topico"] = d["temas"][0]
        state["temas_hash"] = th
    escopo = carregar_scopus(cfg)
    comp = compilar_facetas(cfg)
    fh = hash_filtros(cfg)
    if state.get("facetas_hash") != fh:
        for d in state.get("arquivo", []):
            d["facetas"] = classificar(d.get("titulo"), d.get("resumo"), comp)
        state["facetas_hash"] = fh
    hist = historico_dias(cfg)
    precisa_historico = bool(hist) and hist > state.get("historico_feito", 0)
    if dias is None:
        dias = hist if precisa_historico else max(int(b["dias_para_tras"]), int(b.get("reprocessar_dias", 30)))
    if dias > 14:   # busca longa (preencher o histórico): olha mais páginas e aceita mais artigos
        limite_topico = min(500, b["max_por_topico"] * math.ceil(dias / 7))
        paginas = b.get("paginas", 3) * min(4, math.ceil(dias / 30))
    else:
        limite_topico = b["max_por_topico"]
        paginas = b.get("paginas", 3)
    erros_busca = 0
    ini = (hoje - timedelta(days=dias)).isoformat()
    fim = hoje.isoformat()

    vistos = set(state.setdefault("vistos", []))
    arquivo = state.setdefault("arquivo", [])
    todos_novos = []
    novas_chaves = set()

    if revistas_modo:   # tudo o que as revistas escolhidas publicaram
        topicos_busca = [{"nome": "Revistas escolhidas", "termos": [], "min": 0,
                          "max": int(b.get("max_por_dia", 3000))}]
    elif amplo:   # uma única busca: tudo que cita abelhas (os temas são etiquetas, não filtros)
        topicos_busca = [{"nome": "Abelhas (tudo)", "termos": termos_abelha(cfg), "min": 0,
                          "max": int(b.get("max_por_dia", 3000))}]
    else:
        topicos_busca = cfg["topicos"]
    for t in topicos_busca:
        recs = []
        if revistas_modo:
            rr, ne = coletar_revistas(cfg, state, ini, fim, b)
            recs += rr
            erros_busca += ne
        if "openalex" in b["fontes"] and not revistas_modo:
            try:
                recs += openalex_search(t, ini, fim, per_page=100,
                                        paginas=(int(b.get("max_paginas", 100)) if amplo else paginas))
            except Exception as e:
                erros_busca += 1
                log(f"Erro OpenAlex ({t['nome']}): {e}")
        if "europepmc" in b["fontes"] and not revistas_modo:
            try:
                recs += epmc_search(t, ini, fim, page_size=1000 if amplo else 100, kw=amplo)
            except Exception as e:
                erros_busca += 1
                log(f"Erro Europe PMC ({t['nome']}): {e}")
        if amplo and _entradas_revistas(cfg, "revistas_de_abelhas"):
            # revistas só de abelhas: entra TUDO que elas publicam (não depende de resumo nem de palavra no título)
            rr, ne = coletar_revistas(cfg, state, ini, fim, b, "revistas_de_abelhas")
            recs = rr + recs
            erros_busca += ne

        recs = dedup(recs)
        if not revistas_modo:   # no modo "revistas" a sua lista de revistas é o único filtro
            recs = [r for r in recs
                    if r.get("completa")
                    or (revista_ok(r["revista"], cfg) and not excluida(r, cfg) and scopus_ok(r, escopo))]
        if amplo or revistas_modo:
            for r in recs:
                r["motivo"] = motivo_de(r, cfg, escopo)
        if amplo:   # rigor: quão exigente é a busca por palavras (config: abelhas > rigor)
            rigor = (cfg.get("abelhas") or {}).get("rigor", "normal")
            antes = len(recs)
            recs = [r for r in recs if passa_rigor(r["motivo"], rigor)]
            if len(recs) != antes:
                log(f"Rigor \"{rigor}\": {antes - len(recs)} artigo(s) descartado(s) por não terem palavra de abelha em lugar forte")
        for r in recs:
            r["score"] = score(r, t)
            if not amplo and not revistas_modo:
                r["motivo"] = {"via": "tema", "tema": t["nome"], "pontos": r["score"]}
        novos = [r for r in recs
                 if r["key"] not in vistos
                 and "t:" + norm_title(r["titulo"]) not in vistos
                 and r["score"] >= int(t.get("min", b["pontuacao_minima"]))]
        novos.sort(key=lambda r: r["data"] or "", reverse=True)
        novos.sort(key=lambda r: r["score"], reverse=True)
        novos = novos[: int(t.get("max") or limite_topico)]
        for r in novos:
            novas_chaves.add(r["key"])
            novas_chaves.add("t:" + norm_title(r["titulo"]))
            r["facetas"] = classificar(r["titulo"], r.get("resumo"), comp)
            if etiquetar:
                r["temas"] = classificar_temas(r, comp_temas)
            r["tardio"] = (not precisa_historico) and (r.get("data") or "")[:10] < (
                hoje - timedelta(days=int(b["dias_para_tras"]))).isoformat()
            reg = para_site(r, r["temas"][0] if etiquetar else t["nome"], "novo", hoje.isoformat())
            arquivo.append(reg)
            todos_novos.append(reg)
        log(f"{t['nome']}: {len(novos)} novos")

    vistos |= novas_chaves
    garantir_fila_classicos(cfg, state)

    arquivo = [d for d in arquivo if na_janela(d, hoje, hist)]
    if precisa_historico and erros_busca == 0:
        state["historico_feito"] = hist
    state["vistos"] = sorted(vistos)
    state["arquivo"] = arquivo[-8000:]

    if enviar and cfg.get("email", {}).get("ativo"):
        titulo = f"Radar de artigos — {hoje.strftime('%d/%m/%Y')}"
        h, t_ = montar_email(titulo, todos_novos)
        if not enviar_email(cfg, f"📚 {titulo} ({len(todos_novos)} novos)", h, t_):
            log("E-mail falhou; o site foi atualizado mesmo assim.")

    gerar_site(cfg, state, hoje)
    save_state(state)
    resumo_custo()


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
                                   per_page=min(100, c["por_topico"]), ate_ano=c.get("ate_ano"))
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
    resumo_custo()


# ----------------------------------------------------------------------------
# Diagnóstico: por que os artigos de uma revista aparecem (ou não) no site
# ----------------------------------------------------------------------------
OPENALEX_FONTES = "https://api.openalex.org/sources"


def _achar_fonte(alvo):
    """Devolve (filtro_openalex, nome_para_mostrar) para um nome ou ISSN de revista."""
    alvo = (alvo or "").strip()
    if re.fullmatch(r"\d{4}-?\d{3}[\dXx]", alvo):
        issn = alvo if "-" in alvo else alvo[:4] + "-" + alvo[4:]
        return f"primary_location.source.issn:{issn}", f"ISSN {issn}"
    params = {"search": alvo, "per-page": 5}
    if os.getenv("OPENALEX_MAILTO"):
        params["mailto"] = os.environ["OPENALEX_MAILTO"]
    dados = get_json(OPENALEX_FONTES, params)
    contar_custo(dados)
    res = dados.get("results", [])
    if not res:
        return None, None
    esc = next((x for x in res if norm_j(x.get("display_name")) == norm_j(alvo)), res[0])
    sid = (esc.get("id") or "").rsplit("/", 1)[-1]
    return f"primary_location.source.id:{sid}", f"{esc.get('display_name')} ({esc.get('issn_l') or 'sem ISSN'})"


def _entrada_da_fonte(cfg, state, filtro_fonte, chave="revistas"):
    """A entrada da lista (config) que corresponde à revista do diagnóstico, ou None."""
    alvo_id = filtro_fonte.rsplit(":", 1)[-1] if ".source.id:" in filtro_fonte else ""
    alvo_issn = _issn_norm(filtro_fonte.rsplit(":", 1)[-1]) if ".issn:" in filtro_fonte else ""
    entrada = None
    for e, i in resolver_todas(cfg, state, chave):
        if (alvo_id and i["id"] == alvo_id) or (alvo_issn and _issn_norm(i["issn"]) == alvo_issn):
            entrada = e
    return entrada


def _diag_revistas(cfg, trabalhos, filtro_fonte, ini, fim, hoje, state, chave="revistas"):
    """Diagnóstico para revistas de lista (modo 'revistas' ou 'revistas_de_abelhas'): o artigo passa nas regras dela?"""
    entrada = _entrada_da_fonte(cfg, state, filtro_fonte, chave)
    so_abelhas = bool(entrada and entrada["so_abelhas"])
    casa = set()
    if so_abelhas:
        base = {"nome": "Abelhas (tudo)", "termos": termos_abelha(cfg)}
        casa = {r["key"] for r in openalex_search(base, ini, fim, per_page=100, paginas=10, extra_filtros=[filtro_fonte])}
    comp_temas = compilar_temas(cfg)
    hist = historico_dias(cfg)
    no_site = {d.get("key") for d in state.get("arquivo", [])}
    vistos = set(state.get("vistos", []))
    linhas = []
    for r in trabalhos:
        if r["tipo"] not in TIPOS_ACEITOS:
            cat, txt = "tipo", f"Tipo \"{r['tipo'] or 'desconhecido'}\" não é aceito (o robô só pega artigo, revisão e preprint)."
        elif entrada is None:
            cat, txt = "lista", f"Esta revista não está na sua lista (config.yaml > {chave})."
        elif so_abelhas and r["key"] not in casa:
            cat, txt = "tema", "A revista está marcada como so_abelhas e o título/resumo não citam abelhas."
        elif not na_janela(r, hoje, hist):
            cat, txt = "janela", "Fora do histórico guardado pelo site."
        elif r["key"] in no_site:
            cat, txt = "ok", "Aparece no site."
        elif r["key"] in vistos:
            cat, txt = "ok", "Passa na triagem (já foi visto; sai do site quando passa do histórico)."
        else:
            cat, txt = "ok", "Passa na triagem: entra no site na próxima execução."
        linhas.append({"r": r, "cat": cat, "txt": txt,
                       "temas": classificar_temas(r, comp_temas) if cat == "ok" else []})
    return linhas


def diagnosticar(cfg, alvo, dias, state=None):
    """Lista os trabalhos da revista e, para cada um, o resultado da triagem do robô."""
    hoje = date.today()
    ini, fim = (hoje - timedelta(days=dias)).isoformat(), hoje.isoformat()
    filtro_fonte, nome_fonte = _achar_fonte(alvo)
    if not filtro_fonte:
        return None, None
    # 1) tudo o que o OpenAlex tem dessa revista na janela, de qualquer tipo
    params = _params_openalex([filtro_fonte, f"from_publication_date:{ini}", f"to_publication_date:{fim}"],
                              "publication_date:desc", 100)
    trabalhos = [_rec_openalex(w) for w in _paginar_openalex(params, 10, 100)]
    if modo_busca(cfg) == "revistas":
        return nome_fonte, _diag_revistas(cfg, trabalhos, filtro_fonte, ini, fim, hoje, state or {})
    if modo_busca(cfg) == "amplo" and _entrada_da_fonte(cfg, state or {}, filtro_fonte, "revistas_de_abelhas"):
        return nome_fonte, _diag_revistas(cfg, trabalhos, filtro_fonte, ini, fim, hoje, state or {}, "revistas_de_abelhas")
    # 2) quais deles a busca REAL de cada tema devolve
    por_tema = {}
    amplo = modo_busca(cfg) == "amplo"
    if amplo:
        base = {"nome": "Abelhas (tudo)", "termos": termos_abelha(cfg), "min": 0}
        try:
            por_tema[base["nome"]] = {r["key"] for r in openalex_search(
                base, ini, fim, per_page=100, paginas=10, extra_filtros=[filtro_fonte])}
        except Exception as e:
            log(f"Erro na busca ampla: {e}")
            por_tema[base["nome"]] = set()
        topicos = {base["nome"]: base}
        comp_temas = compilar_temas(cfg)
    else:
        for t in cfg["topicos"]:
            try:
                recs = openalex_search(t, ini, fim, paginas=3, extra_filtros=[filtro_fonte])
            except Exception as e:
                log(f"Erro no tema {t['nome']}: {e}")
                recs = []
            por_tema[t["nome"]] = {r["key"] for r in recs}
        topicos = {t["nome"]: t for t in cfg["topicos"]}
    escopo = carregar_scopus(cfg)
    hist = historico_dias(cfg)
    minimo = cfg["busca"]["pontuacao_minima"]
    state = state or {}
    no_site = {d.get("key") for d in state.get("arquivo", [])}
    vistos = set(state.get("vistos", []))

    linhas = []
    for r in trabalhos:
        temas = [n for n, ks in por_tema.items() if r["key"] in ks]
        if r["tipo"] not in TIPOS_ACEITOS:
            cat, txt = "tipo", f"Tipo \"{r['tipo'] or 'desconhecido'}\" não é aceito (o robô só pega artigo, revisão e preprint)."
        elif not temas:
            extra = " O OpenAlex não tem o resumo deste trabalho, então só o título foi analisado." if not r["resumo"] else ""
            if amplo:
                cat, txt = "tema", "O título e o resumo não citam abelhas (palavras: " + ", ".join(termos_abelha(cfg)) + ")." + extra
            else:
                cat, txt = "tema", "Nenhum tema casou: o título e o resumo não trazem as palavras dos seus tópicos." + extra
        else:
            pontos = {n: score(r, topicos[n]) for n in temas}
            melhor = max(pontos.values())
            if not any(p >= int(topicos[n].get("min", minimo)) for n, p in pontos.items()):
                cat, txt = "pontos", f"Pontuação baixa ({melhor}; mínimo {minimo}): as palavras só aparecem no resumo, não no título."
            elif excluida(r, cfg):
                cat, txt = "apis", "Excluído pela regra de Apis mellifera / honey bee (aparece no título)."
            elif not revista_ok(r["revista"], cfg):
                cat, txt = "lista", "Fora da sua lista de revistas (filtro_revistas)."
            elif not scopus_ok(r, escopo):
                cat, txt = "scopus", "A revista não está na lista da Scopus (ou está inativa)."
            elif not na_janela(r, hoje, hist):
                cat, txt = "janela", "Fora do histórico guardado pelo site."
            else:
                if r["key"] in no_site:
                    cat, txt = "ok", "Aparece no site."
                elif r["key"] in vistos:
                    cat, txt = "ok", "Passa na triagem (já foi visto; sai do site quando passa do histórico)."
                else:
                    cat, txt = "ok", "Passa na triagem: entra no site na próxima execução."
        if amplo and temas:
            temas = classificar_temas(r, comp_temas)   # etiquetas de tema que o artigo receberia
        linhas.append({"r": r, "cat": cat, "txt": txt, "temas": temas})
    return nome_fonte, linhas


ROTULOS_DIAG = {
    "ok": ("Aparecem", "#2F7D4F"), "apis": ("Barrados: Apis mellifera / honey bee no título", "#B26A00"),
    "tema": ("Barrados: nenhuma palavra de busca casou", "#B3261E"), "pontos": ("Barrados: pontuação baixa", "#B3261E"),
    "tipo": ("Barrados: tipo de documento", "#B3261E"), "lista": ("Barrados: fora da sua lista de revistas", "#7C6F48"),
    "scopus": ("Barrados: fora da Scopus", "#7C6F48"), "janela": ("Fora do histórico", "#7C6F48"),
}


def relatorio_diagnostico(nome_fonte, linhas, dias):
    cont = {}
    for l in linhas:
        cont[l["cat"]] = cont.get(l["cat"], 0) + 1
    resumo = "".join(
        f"<li><b style='color:{ROTULOS_DIAG[c][1]}'>{cont[c]}</b> — {html.escape(ROTULOS_DIAG[c][0])}</li>"
        for c in ROTULOS_DIAG if c in cont)
    linhas_html = "".join(
        "<tr><td>{d}</td><td>{t}</td><td>{oa}</td><td><a href='{u}'>{ti}</a><div class='m'>{te}</div></td><td style='color:{cor}'>{tx}</td></tr>".format(
            d=html.escape(l["r"]["data"]), t=html.escape(l["r"]["tipo"] or "?"), u=html.escape(l["r"]["url"]),
            oa="sim" if l["r"].get("oa") else "não",
            ti=html.escape(l["r"]["titulo"]), te=html.escape(", ".join(l["temas"]) or ""),
            cor=ROTULOS_DIAG[l["cat"]][1], tx=html.escape(l["txt"]))
        for l in linhas)
    n_oa = sum(1 for l in linhas if l["r"].get("oa"))
    sem_res = [l for l in linhas if not l["r"].get("resumo")]
    sem_res_fechados = sum(1 for l in sem_res if not l["r"].get("oa"))
    acesso = (f"<p>Acesso aberto: <b>{n_oa}</b> de {len(linhas)}. Sem resumo no OpenAlex: <b>{len(sem_res)}</b> "
              f"(<b>{sem_res_fechados}</b> deles não são acesso aberto — algumas editoras, como a Springer Nature, "
              f"não deixam o OpenAlex mostrar o resumo de artigos fechados).</p>")
    return f"""<!doctype html><html lang="pt-BR"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>Diagnóstico — {html.escape(nome_fonte)}</title>
<style>body{{font-family:-apple-system,Segoe UI,Roboto,Arial,sans-serif;max-width:1100px;margin:24px auto;padding:0 16px;color:#2A2208;background:#FFFDF5}}
h1{{font-size:22px}}table{{border-collapse:collapse;width:100%;font-size:14px}}td,th{{border-bottom:1px solid #F1E7C6;padding:8px;text-align:left;vertical-align:top}}
th{{background:#FFF7DB}}.m{{font-size:12px;color:#7C6F48}}a{{color:#8A5E00}}</style></head><body>
<h1>Diagnóstico: {html.escape(nome_fonte)}</h1>
<p>Trabalhos que o OpenAlex tem dessa revista nos últimos {dias} dias: <b>{len(linhas)}</b>. Gerado em {date.today().strftime('%d/%m/%Y')}.</p>
<ul>{resumo}</ul>
{acesso}
<table><tr><th>Data</th><th>Tipo</th><th>Acesso aberto</th><th>Título</th><th>Resultado</th></tr>{linhas_html}</table>
<p class="m">Se um artigo que você viu no site da revista nem aparece nesta lista, o OpenAlex ainda não o indexou.</p>
</body></html>"""


def _parece_artigo(alvo):
    a = (alvo or "").strip()
    return bool(re.search(r"10\.\d{4,9}/\S+", a) or re.search(r"openalex\.org/W\d+", a, re.I)
                or re.fullmatch(r"W\d+", a, re.I))


def buscar_artigo(alvo):
    a = alvo.strip()
    m = re.search(r"10\.\d{4,9}/\S+", a)
    if m:
        data = get_json(f"{OPENALEX_URL}/https://doi.org/{m.group(0)}", _auth_openalex())
    else:
        wid = re.search(r"W\d+", a, re.I).group(0).upper()
        data = get_json(f"{OPENALEX_URL}/{wid}", _auth_openalex())
    contar_custo(data)
    return _rec_openalex(data) if data.get("id") else None


def _dias_desde(iso, hoje):
    try:
        return (hoje - date.fromisoformat((iso or "")[:10])).days
    except ValueError:
        return None


def avaliar_artigo(r, cfg, state, hoje=None):
    """Lista de verificações [(nome, ok, detalhe)] que o robô faria com este artigo."""
    hoje = hoje or date.today()
    b = cfg["busca"]
    modo = modo_busca(cfg)
    escopo = carregar_scopus(cfg)
    hist = historico_dias(cfg)
    lookback = max(int(b["dias_para_tras"]), int(b.get("reprocessar_dias", 30)))
    texto = ((r.get("titulo") or "") + " " + (r.get("resumo") or "")).lower()
    no_site = any(d.get("key") == r["key"] for d in state.get("arquivo", []))
    visto = r["key"] in set(state.get("vistos", []))
    checks = []

    def ver(nome, ok, detalhe):
        checks.append({"nome": nome, "ok": bool(ok), "detalhe": detalhe})

    ver("Tipo de documento", r["tipo"] in TIPOS_ACEITOS,
        f"O OpenAlex classifica como \"{r['tipo'] or 'desconhecido'}\". O robô só aceita: {', '.join(TIPOS_ACEITOS)}.")
    d_pub = _dias_desde(r["data"], hoje)
    d_cad = _dias_desde(r.get("criado"), hoje)
    atraso = (d_pub - d_cad) if (d_pub is not None and d_cad is not None) else None
    pega = no_site or visto or (d_pub is not None and d_pub <= lookback)
    det = f"Publicado em {r['data'] or '?'}"
    if r.get("criado"):
        det += f"; cadastrado no OpenAlex em {r['criado']}"
        if atraso is not None and atraso > 0:
            det += f" ({atraso} dias depois)"
    det += f". A busca diária olha os últimos {lookback} dias (config: dias_para_tras / reprocessar_dias)."
    ver("A busca diária alcança a data", pega, det)
    ver("Dentro do histórico do site", na_janela(r, hoje, hist),
        f"O site guarda {hist or 'todos os'} dias de histórico (config: site > historico_dias).")

    em_lista = None
    if modo == "revistas":
        chave, passa_texto_so = "revistas", True
    elif modo == "amplo" and _entradas_revistas(cfg, "revistas_de_abelhas"):
        chave, passa_texto_so = "revistas_de_abelhas", False
    else:
        chave, passa_texto_so = None, False
    if chave:
        issns = {_issn_norm(i) for i in r.get("issn") or []}
        for e, info in resolver_todas(cfg, state, chave):
            if (info["id"] == r.get("fonte_id")) or (_issn_norm(info.get("issn")) in issns and issns):
                em_lista = e
        if modo == "revistas":
            ver("Revista está na sua lista (config.yaml > revistas)", em_lista is not None,
                "A revista deste artigo " + ("está" if em_lista else "NÃO está") + " na lista.")
        else:
            ver("Revista só de abelhas (lista revistas_de_abelhas)", True,
                "Esta revista ESTÁ na lista: entra tudo o que ela publica, sem olhar palavras nem a Scopus." if em_lista
                else "Esta revista não está na lista; o artigo segue para as verificações de palavras e da Scopus.")
    entra_pela_lista = bool(em_lista) and not em_lista["so_abelhas"]

    if modo == "revistas":
        if em_lista and em_lista["so_abelhas"]:
            ok = any(_padrao(t).search(texto) for t in termos_abelha(cfg))
            ver("Cita abelhas no título ou resumo", ok, "A revista está marcada com so_abelhas.")
    elif not entra_pela_lista:
        if modo == "amplo":
            termos = termos_abelha(cfg)
            ok = any(_padrao(t).search(texto) for t in termos)
            sem_res = not (r.get("resumo") or "").strip()
            m_ = motivo_de(r, cfg)
            rigor_ = (cfg.get("abelhas") or {}).get("rigor", "normal")
            ver("Rigor da busca (abelhas > rigor: " + str(rigor_) + ")", passa_rigor(m_, rigor_),
                "Termos achados: " + (", ".join(f"{t} ({l})" for t, l in m_["achou"]) or "nenhum escrito no título/resumo (o OpenAlex pode ter achado por variação da palavra)")
                + ". normal = qualquer termo; medio = termo no título ou 2 termos diferentes; alto = termo no título/palavras-chave.")
            ver("Cita abelhas no título ou resumo", ok,
                f"Palavras procuradas: {', '.join(termos)}."
                + (" O OpenAlex NÃO tem o resumo deste artigo (editoras como Springer Nature e Elsevier não liberam o resumo de artigos fechados), então só o título foi analisado." if sem_res else ""))
        else:
            ver("Casa com algum tema (modo por_tema)", any(
                (any(_padrao(t).search(texto) for t in tp["termos"]) and any(_padrao(c).search(texto) for c in (tp.get("contexto") or [])))
                and score(r, tp) >= int(tp.get("min", b["pontuacao_minima"])) for tp in cfg["topicos"]),
                "Verificação local aproximada dos seus tópicos e da pontuação mínima.")
        ver("Revista na lista da Scopus", scopus_ok(r, escopo),
            "Filtro da Scopus desligado ou sem arquivo (passa)." if escopo is None else
            f"Revista \"{r['revista']}\" (ISSN {', '.join(r.get('issn') or []) or 'sem ISSN no OpenAlex'}) "
            + ("está" if scopus_ok(r, escopo) else "NÃO está") + " na planilha da Scopus (só revistas ativas do tipo Journal).")
        ver("Sua lista de revistas (filtro_revistas)", revista_ok(r["revista"], cfg), "Só vale se filtro_revistas > ativo for true.")
        ver("Regra do Apis mellifera (excluir)", not excluida(r, cfg), "Só vale se excluir > termos tiver palavras.")
    return checks, no_site, visto, entra_pela_lista


def run_diagnostico_artigo(cfg, alvo):
    state = load_state()
    r = buscar_artigo(alvo)
    if not r:
        log(f"Não encontrei o artigo \"{alvo}\" no OpenAlex.")
        return
    checks, no_site, visto, pela_lista = avaliar_artigo(r, cfg, state)
    falhas = [c for c in checks if not c["ok"]]
    entra = not falhas
    linhas = "".join(
        "<tr><td>{i}</td><td>{n}</td><td style='color:{cor}'><b>{v}</b></td><td>{d}</td></tr>".format(
            i="✔" if c["ok"] else "✘", n=html.escape(c["nome"]), cor="#2F7D4F" if c["ok"] else "#B3261E",
            v="passa" if c["ok"] else "BARRA", d=html.escape(c["detalhe"])) for c in checks)
    veredito = ("Este artigo PASSA em todas as verificações" + (" e já está no site." if no_site else
                " (se ainda não está no site, ele entra na próxima execução)." if not visto else
                " e já foi visto pelo robô (sai do site quando passa do histórico)."))\
        if entra else f"Este artigo NÃO entra no site: {len(falhas)} verificação(ões) barram — " + "; ".join(c["nome"] for c in falhas) + "."
    DOCS_DIR.mkdir(exist_ok=True)
    (DOCS_DIR / "diagnostico.html").write_text(f"""<!doctype html><html lang="pt-BR"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>Diagnóstico do artigo</title><style>body{{font-family:-apple-system,Segoe UI,Roboto,Arial,sans-serif;max-width:1000px;margin:24px auto;padding:0 16px;color:#2A2208;background:#FFFDF5}}
table{{border-collapse:collapse;width:100%;font-size:14px}}td,th{{border-bottom:1px solid #F1E7C6;padding:8px;text-align:left;vertical-align:top}}th{{background:#FFF7DB}}a{{color:#8A5E00}}.v{{font-size:17px;padding:12px;border-radius:10px;background:#FFF7DB}}</style></head><body>
<h1>Diagnóstico do artigo</h1>
<p><a href="{html.escape(r['url'])}">{html.escape(r['titulo'])}</a><br>Revista: <b>{html.escape(r['revista'] or '?')}</b> · Tipo: {html.escape(r['tipo'] or '?')} · Acesso aberto: {'sim' if r.get('oa') else 'não'} · Resumo no OpenAlex: {'sim' if r['resumo'] else 'não'}</p>
<p class="v">{html.escape(veredito)}</p>
<table><tr><th></th><th>Verificação</th><th>Resultado</th><th>Detalhe</th></tr>{linhas}</table></body></html>""", encoding="utf-8")
    log(f"=== Diagnóstico do artigo: {r['titulo'][:80]} ===")
    for c in checks:
        log(f"  {'✔' if c['ok'] else '✘'} {c['nome']}: {c['detalhe'][:160]}")
    log(veredito)
    resumo_custo()


def run_diagnostico(cfg, alvo, dias):
    aviso_chave()
    if _parece_artigo(alvo):   # DOI, id do OpenAlex ou link: diagnostica um único artigo
        return run_diagnostico_artigo(cfg, alvo)
    dias = dias or 60
    state = load_state()
    nome_fonte, linhas = diagnosticar(cfg, alvo, dias, state)
    if not nome_fonte:
        log(f"Não encontrei a revista \"{alvo}\" no OpenAlex.")
        return
    DOCS_DIR.mkdir(exist_ok=True)
    (DOCS_DIR / "diagnostico.html").write_text(relatorio_diagnostico(nome_fonte, linhas, dias), encoding="utf-8")
    cont = {}
    for l in linhas:
        cont[l["cat"]] = cont.get(l["cat"], 0) + 1
    log(f"=== Diagnóstico: {nome_fonte} — últimos {dias} dias: {len(linhas)} trabalhos ===")
    log(f"    acesso aberto: {sum(1 for l in linhas if l['r'].get('oa'))} | sem resumo no OpenAlex: "
        f"{sum(1 for l in linhas if not l['r'].get('resumo'))}")
    for c in ROTULOS_DIAG:
        if c in cont:
            log(f"{cont[c]:4d}  {ROTULOS_DIAG[c][0]}")
    log("Relatório completo: docs/diagnostico.html (abra no site: .../diagnostico.html)")
    resumo_custo()


# ----------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser(description="Radar de artigos científicos")
    ap.add_argument("modo", choices=["diario", "classicos", "diagnostico"])
    ap.add_argument("alvo", nargs="?", help="(diagnostico) nome ou ISSN da revista")
    ap.add_argument("--dias", type=int, help="janela de busca em dias")
    ap.add_argument("--sem-email", action="store_true", help="não envia e-mail")
    args = ap.parse_args()

    cfg = load_config()
    if args.modo == "classicos":
        run_classicos(cfg)
    elif args.modo == "diagnostico":
        run_diagnostico(cfg, args.alvo or "Apidologie", args.dias)
    else:
        run_diario(cfg, load_state(), args.dias, enviar=not args.sem_email)


if __name__ == "__main__":
    main()
