"""
Acompanha processos no eproc do TJRJ (1º grau), registra os eventos num Google Doc por processo e
manda um e-mail quando aparece movimentação nova.

Para cada processo digitado:
  1. abre "Consulta Processual" > "Consultar Processos";
  2. digita o número em "Número do processo" e clica em "Consultar";
  3. lê a tabela de eventos e compara com o último evento visto na execução anterior;
  4. se houver eventos novos, abre os documentos anexados a eles (links "infraLinkDocumento"),
     salva uma cópia e lê o texto;
  5. no Google Drive, dentro de NOME_PASTA_DRIVE, cada processo tem a sua pasta "Processo <número>"
     com as atualizações dele: o Google Doc do processo e os documentos dos eventos novos.
     O Doc é criado na 1ª vez só com o último evento; depois, cada evento novo é acrescentado no
     mesmo Doc, no topo da lista (o mais recente primeiro; o que alguém escrever no Doc é mantido),
     com link para os documentos na pasta;
  6. no fim, manda UM e-mail (para EMAIL_DESTINO) com cada evento novo, o texto dos documentos e
     os links. Sem mudanças, o e-mail sai do mesmo jeito, com o último evento de cada processo
     (EMAIL_SEMPRE = False: só manda quando houver mudança).
No eproc só lê: não peticiona, não marca nada e não altera nada no sistema.

Precisa do Google Chrome instalado e de:
  pip install playwright pymupdf google-api-python-client google-auth-oauthlib

Google: na 1ª vez o robô abre o navegador para você entrar na conta Google e autorizar (a senha
fica só com o Google). ENTRE COM A CONTA QUE VAI MANDAR OS E-MAILS (a da Conceito): o e-mail sai
dela e vai para EMAIL_DESTINO. Antes disso é preciso criar o arquivo de acesso (client_secret_...json):
rode o robô que ele explica o passo a passo.
  USAR_GOOGLE_DOCS = False  só o e-mail (sem Google Doc e sem Drive).
  USAR_GOOGLE = False       nada do Google: só o relatório .txt, sem e-mail.

Navegador (NAVEGADOR, abaixo):
  "chrome"   abre um Chrome com perfil próprio do robô (padrão).
  "firefox"  usa o SEU Firefox, com o seu perfil. O Firefox não deixa ser controlado depois de
             aberto: o robô pede para fechá-lo e o abre de novo em modo de controle.
             Precisa também de: pip install selenium

Uso:
  python consulta_eproc.py

Login: você faz o login na janela que o robô abriu; ele continua sozinho quando o menu do eproc
aparecer.
Os números podem ser digitados ou colados, um por linha ou separados por vírgula, espaço ou ';'.
Linha vazia termina a digitação.

Arquivos (em Downloads/processos/eproc):
  estado.json                 último evento visto de cada processo e ids do Google (a "memória")
  relatorios/relatorio_*.txt  um relatório por execução
  relatorios/email_*.html     cópia de cada e-mail montado
  documentos/<processo>/      cópia dos documentos dos eventos novos
  google/credentials.json     acesso ao Google (você cria; veja acima)
  google/token.json           autorização da conta (criado sozinho no 1º login)

Primeira vez de um processo: o robô ainda não sabe o que já foi visto. Ele trata como novos os
últimos PRIMEIRA_VEZ_EVENTOS eventos (padrão 1) e guarda o resto como já visto.
"""
import base64
import json
import os
import re
import shutil
import subprocess
import time
from datetime import datetime
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import urljoin, urlparse
from urllib.request import urlopen

# Endereço do eproc. Ele redireciona sozinho para a tela de login (SSO).
URL_EPROC = "https://eproc1g.tjrj.jus.br/eproc/"

PASTA_BASE = Path.home() / "Downloads" / "processos" / "eproc"
PASTA_PERFIL_CHROME = Path.home() / "Downloads" / "processos" / "perfil_chrome_eproc"
ARQUIVO_ESTADO = PASTA_BASE / "estado.json"
PASTA_RELATORIOS = PASTA_BASE / "relatorios"
PASTA_DOCUMENTOS = PASTA_BASE / "documentos"
PORTA_CHROME = 9223  # diferente da do e-SISREC (9222), para os dois robôs não se misturarem

PORTA_FIREFOX = 2828  # porta padrão do modo de controle do Firefox (Marionette)

# Navegador usado: "chrome" (perfil próprio do robô) ou "firefox" (o seu Firefox, com o seu perfil).
NAVEGADOR = "chrome"

# Google Docs/Drive/Gmail. False = só o relatório .txt, sem Google e sem e-mail.
USAR_GOOGLE = True
# Google Doc por processo + cópia dos documentos no Drive. False = só manda o e-mail.
USAR_GOOGLE_DOCS = True
PASTA_GOOGLE = PASTA_BASE / "google"
NOME_PASTA_DRIVE = "Acompanhamento eproc"
# Quem recebe o e-mail das mudanças. Ex.: ["fulano@gmail.com", "escritorio@exemplo.com"]
EMAIL_DESTINO: list[str] = ["pedrgtsantos@gmail.com"]
# Mandar e-mail também na primeira consulta de um processo (quando ainda não há "mudança")?
EMAIL_NA_PRIMEIRA_VEZ = False
# Mandar o e-mail em toda execução, mesmo sem mudanças (com o resumo de cada processo)?
EMAIL_SEMPRE = True

ESPERA_MS = 60_000

# Na primeira vez que um processo é consultado, quantos dos últimos eventos entram no relatório.
PRIMEIRA_VEZ_EVENTOS = 1
# Máximo de caracteres do texto de cada documento no relatório (0 = sem limite).
LIMITE_TEXTO = 8000

SELETOR_MENU_PAI = "a[aria-label='Consulta Processual']"
SELETOR_MENU = "a[aria-label='Consultar Processos']"
SELETOR_CAMPO = "input#numNrProcesso"
SELETOR_BOTAO = "button#sbmConsultar"
SELETOR_EVENTO = "td.infraEventoDescricao"
SELETOR_LINK_PROCESSO = "a[href*='processo_selecionar']"


def agora() -> str:
    return datetime.now().strftime("%d/%m/%Y %H:%M:%S")


def erro_curto(e: Exception) -> str:
    """Só a 1ª linha do erro (o Playwright junta um 'Call log' enorme)."""
    return (str(e).strip().splitlines() or [type(e).__name__])[0]


def so_digitos(texto: str) -> str:
    return re.sub(r"\D", "", texto or "")


# ---------------------------------------------------------------------------
# Chrome
# ---------------------------------------------------------------------------

def encontrar_chrome() -> str | None:
    """Caminho do Chrome (ou do Edge, se não houver Chrome). CHROME_PATH tem prioridade."""
    candidatos = [os.getenv("CHROME_PATH"), shutil.which("chrome"), shutil.which("msedge")]
    for base in (os.getenv("PROGRAMFILES"), os.getenv("PROGRAMFILES(X86)"), os.getenv("LOCALAPPDATA")):
        if base:
            candidatos.append(os.path.join(base, "Google", "Chrome", "Application", "chrome.exe"))
    for base in (os.getenv("PROGRAMFILES(X86)"), os.getenv("PROGRAMFILES")):
        if base:
            candidatos.append(os.path.join(base, "Microsoft", "Edge", "Application", "msedge.exe"))
    return next((c for c in candidatos if c and os.path.isfile(c)), None)


def endereco_chrome() -> str | None:
    """Endereço da porta de conexão do Chrome do robô, ou None se ele não estiver aberto."""
    for host in ("127.0.0.1", "[::1]"):
        endereco = f"http://{host}:{PORTA_CHROME}"
        try:
            with urlopen(f"{endereco}/json/version", timeout=2):
                return endereco
        except Exception:
            pass
    return None


def abrir_chrome():
    """Abre um Chrome normal (não controlado pelo robô) já no eproc, para você fazer o login."""
    if endereco_chrome():
        print(f"Chrome do robô já está aberto (porta {PORTA_CHROME}); usando ele.")
        return
    chrome = encontrar_chrome()
    if not chrome:
        raise SystemExit("Chrome não encontrado. Instale o Google Chrome ou defina CHROME_PATH "
                         "com o caminho do chrome.exe.")
    PASTA_PERFIL_CHROME.mkdir(parents=True, exist_ok=True)
    subprocess.Popen([chrome,
                      f"--remote-debugging-port={PORTA_CHROME}",  # só aceita conexões deste computador
                      f"--user-data-dir={PASTA_PERFIL_CHROME}",
                      "--no-first-run", "--no-default-browser-check",
                      URL_EPROC])
    limite = time.monotonic() + 30
    while not endereco_chrome():
        if time.monotonic() > limite:
            raise SystemExit(f"O Chrome abriu, mas a porta {PORTA_CHROME} não respondeu. Se já havia "
                             f"um Chrome com este perfil aberto, feche-o e rode de novo.")
        time.sleep(0.5)


def pagina_do_eproc(url: str) -> bool:
    host = urlparse(url).netloc
    return "eproc" in host and "sso" not in host


def esperar_login(context):
    """Espera, sem limite de tempo, alguma aba do eproc mostrar o menu 'Consultar Processos'."""
    print("=" * 60)
    print("Faça o login no eproc na janela do Chrome que abriu.")
    print("O robô continua sozinho quando aparecer o Painel (menu 'Consulta Processual').")
    print("=" * 60)
    while True:
        for page in list(context.pages):
            if not pagina_do_eproc(page.url):
                continue
            try:
                if page.locator(SELETOR_MENU).count() > 0:
                    print("Login detectado.")
                    return page
            except Exception:
                pass  # a aba estava trocando de página
        try:
            (context.pages[0] if context.pages else context.new_page()).wait_for_timeout(1000)
        except Exception:
            time.sleep(1)


# ---------------------------------------------------------------------------
# Consulta
# ---------------------------------------------------------------------------

class Robo:
    def __init__(self, page):
        self.page = page
        self.url_consulta: str | None = None  # endereço da tela de consulta, guardado na 1ª vez

    def abrir_consulta(self):
        """Consulta Processual > Consultar Processos. Na 2ª vez em diante, volta direto ao endereço."""
        page = self.page
        campo = page.locator(SELETOR_CAMPO)
        if self.url_consulta:
            page.goto(self.url_consulta)
            campo.wait_for(state="visible", timeout=ESPERA_MS)
            return

        item = page.locator(SELETOR_MENU).first
        href = item.evaluate("a => a.href")  # endereço completo (com o hash da sessão)
        try:
            if not item.is_visible():
                page.locator(SELETOR_MENU_PAI).or_(
                    page.get_by_role("link", name="Consulta Processual", exact=True)).first.click(timeout=10_000)
            item.click(timeout=10_000)
            try:
                campo.wait_for(state="visible", timeout=8_000)
            except Exception:
                # O "Consultar Processos" abriu um submenu: clica no de dentro dele.
                alvo = item.get_attribute("data-target")
                sub = page.locator(f"{alvo} a").filter(has_text="Consultar Processos").first
                sub.click(timeout=10_000)
                campo.wait_for(state="visible", timeout=ESPERA_MS)
        except Exception as e:
            print(f"Não consegui pelo menu ({type(e).__name__}); abrindo a tela de consulta direto.")
            page.goto(href)
            campo.wait_for(state="visible", timeout=ESPERA_MS)
        self.url_consulta = page.url

    def abrir_processo(self, numero: str):
        """Digita o número, clica em Consultar e chega à tela do processo (com os eventos)."""
        page = self.page
        self.abrir_consulta()
        campo = page.locator(SELETOR_CAMPO)
        campo.fill("")
        campo.fill(numero)
        page.locator(SELETOR_BOTAO).click()

        eventos = page.locator(SELETOR_EVENTO)
        try:
            page.locator(SELETOR_EVENTO).or_(page.locator(SELETOR_LINK_PROCESSO)).first.wait_for(
                state="attached", timeout=ESPERA_MS)
        except Exception:
            raise RuntimeError("processo não encontrado (a consulta não mostrou o processo nem uma "
                               "lista de resultados). Confira o número.") from None
        if eventos.count() == 0:
            # Caiu numa lista de resultados: abre o processo com o mesmo número.
            links = page.locator(SELETOR_LINK_PROCESSO)
            alvo = links.first
            for i in range(links.count()):
                if so_digitos(numero) and so_digitos(numero) in so_digitos(links.nth(i).inner_text()):
                    alvo = links.nth(i)
                    break
            alvo.click()
            eventos.first.wait_for(state="attached", timeout=ESPERA_MS)

    def ler_eventos(self) -> list[dict]:
        """Lê a tabela de eventos: número, data, descrição e links dos documentos de cada um."""
        return montar_eventos(self.page.evaluate(JS_EVENTOS))

    def baixar(self, url: str) -> tuple[bytes, str]:
        """Baixa um endereço com o login do navegador. Devolve (conteúdo, content-type)."""
        return resultado_download(self.page.evaluate(JS_BAIXAR, url))


# Código que roda dentro da página (igual no Chrome e no Firefox).
JS_EVENTOS = """() =>
    [...document.querySelectorAll('td.infraEventoDescricao')].map(td => {
        const tr = td.closest('tr');
        return {
            id: tr.id || '',
            parte: tr.dataset.parte || '',
            celulas: [...tr.children].map(c => c.innerText.trim()),
            descricao: td.innerText.trim(),
            docs: [...tr.querySelectorAll('a.infraLinkDocumento')].map(a => ({
                nome: (a.innerText || a.title || '').trim(),
                titulo: (a.title || '').trim(),
                href: a.href,
            })),
        };
    })"""

# O download é feito de dentro da própria aba do eproc, para ir com o seu login.
JS_BAIXAR = """async url => {
    const r = await fetch(url, {credentials: 'include'});
    const bytes = new Uint8Array(await r.arrayBuffer());
    let bin = '';
    for (let i = 0; i < bytes.length; i += 32768)
        bin += String.fromCharCode(...bytes.subarray(i, i + 32768));
    return {ok: r.ok, status: r.status, tipo: r.headers.get('content-type') || '', b64: btoa(bin)};
}"""


def montar_eventos(linhas: list[dict]) -> list[dict]:
    eventos = []
    for linha in linhas:
        # Número do evento: vem do id da linha (<tr id="trEvento46">); senão, da 1ª coluna numérica.
        m = re.fullmatch(r"trEvento(\d+)", linha["id"])
        numero = int(m.group(1)) if m else next((int(c) for c in linha["celulas"] if c.isdigit()), None)
        data = next((d.group(0) for c in linha["celulas"]
                     if (d := re.search(r"\d{2}/\d{2}/\d{4}( \d{2}:\d{2}(:\d{2})?)?", c))), "")
        if numero is None:
            continue
        eventos.append({"numero": numero, "data": data, "descricao": linha["descricao"],
                        "parte": linha["parte"], "docs": linha["docs"]})
    eventos.sort(key=lambda e: e["numero"])
    return eventos


def resultado_download(resultado: dict) -> tuple[bytes, str]:
    if resultado.get("erro"):
        raise RuntimeError(f"falha ao baixar: {resultado['erro']}")
    if not resultado["ok"]:
        raise RuntimeError(f"o eproc respondeu HTTP {resultado['status']}")
    return base64.b64decode(resultado["b64"]), resultado["tipo"]


# ---------------------------------------------------------------------------
# Firefox (o seu Firefox normal, com o seu perfil, aberto em modo de controle)
# ---------------------------------------------------------------------------

def encontrar_firefox() -> str | None:
    """Caminho do Firefox. FIREFOX_PATH tem prioridade. Serve também o Firefox da Microsoft Store."""
    candidatos = [os.getenv("FIREFOX_PATH"), shutil.which("firefox")]
    if os.getenv("LOCALAPPDATA"):
        candidatos.append(os.path.join(os.getenv("LOCALAPPDATA"), "Microsoft", "WindowsApps", "firefox.exe"))
    for base in (os.getenv("PROGRAMFILES"), os.getenv("PROGRAMFILES(X86)")):
        if base:
            candidatos.append(os.path.join(base, "Mozilla Firefox", "firefox.exe"))
    return next((c for c in candidatos if c and os.path.exists(c)), None)


def firefox_rodando() -> bool:
    saida = subprocess.run(["tasklist", "/FI", "IMAGENAME eq firefox.exe", "/NH"],
                           capture_output=True, text=True, errors="replace").stdout
    return "firefox.exe" in saida.lower()


def porta_aberta(porta: int) -> bool:
    import socket
    with socket.socket() as s:
        s.settimeout(1)
        return s.connect_ex(("127.0.0.1", porta)) == 0


def abrir_firefox(argumentos_extras: list[str] | None = None):
    """Abre o seu Firefox em modo de controle (-marionette). Ele não pode estar aberto antes:
    um Firefox aberto do jeito normal não aceita ser controlado."""
    if porta_aberta(PORTA_FIREFOX):
        print(f"Firefox em modo de controle já está aberto (porta {PORTA_FIREFOX}); usando ele.")
        return
    if firefox_rodando():
        print("=" * 60)
        print("FECHE TODAS AS JANELAS DO FIREFOX.")
        print("O robô precisa abrir o Firefox de novo, em modo de controle (com o seu perfil,")
        print("então seus logins e certificados continuam lá). Ele espera você fechar.")
        print("=" * 60)
        while firefox_rodando():
            time.sleep(1)
        time.sleep(2)  # o Firefox termina de gravar o perfil
    firefox = encontrar_firefox()
    if not firefox:
        raise SystemExit("Firefox não encontrado. Defina FIREFOX_PATH com o caminho do firefox.exe.")
    subprocess.Popen([firefox, "-marionette", *(argumentos_extras or []), URL_EPROC])
    limite = time.monotonic() + 60
    while not porta_aberta(PORTA_FIREFOX):
        if time.monotonic() > limite:
            raise SystemExit(f"O Firefox abriu, mas a porta {PORTA_FIREFOX} não respondeu. Feche o "
                             f"Firefox e rode de novo.")
        time.sleep(0.5)


def conectar_firefox():
    """Conecta o Selenium ao Firefox já aberto (geckodriver --connect-existing)."""
    from selenium import webdriver
    from selenium.webdriver.firefox.service import Service

    servico = Service(service_args=["--connect-existing", "--marionette-port", str(PORTA_FIREFOX)])
    driver = webdriver.Firefox(service=servico)
    driver.set_script_timeout(ESPERA_MS / 1000)
    return driver


def esperar_login_firefox(driver):
    """Espera, sem limite de tempo, alguma aba do eproc mostrar o menu 'Consultar Processos'."""
    from selenium.webdriver.common.by import By

    print("=" * 60)
    print("Faça o login no eproc na janela do Firefox (a que tem o ícone de robô na barra).")
    print("O robô continua sozinho quando aparecer o Painel (menu 'Consulta Processual').")
    print("=" * 60)
    while True:
        for aba in driver.window_handles:
            try:
                driver.switch_to.window(aba)
                if pagina_do_eproc(driver.current_url) and driver.find_elements(By.CSS_SELECTOR, SELETOR_MENU):
                    print("Login detectado.")
                    return
            except Exception:
                pass  # a aba estava trocando de página ou foi fechada
        time.sleep(1)


class RoboFirefox:
    """O mesmo que o Robo (Chrome), mas pelo Selenium no Firefox."""

    def __init__(self, driver):
        self.driver = driver
        self.url_consulta: str | None = None

    def _esperar(self, condicao, segundos: float = ESPERA_MS / 1000):
        from selenium.webdriver.support.ui import WebDriverWait
        return WebDriverWait(self.driver, segundos, poll_frequency=0.3).until(condicao)

    def _achar(self, css: str):
        from selenium.webdriver.common.by import By
        return self.driver.find_elements(By.CSS_SELECTOR, css)

    def _campo_visivel(self, segundos: float = ESPERA_MS / 1000):
        return self._esperar(lambda d: next((c for c in self._achar(SELETOR_CAMPO) if c.is_displayed()), False),
                             segundos)

    def abrir_consulta(self):
        from selenium.webdriver.common.by import By
        d = self.driver
        if self.url_consulta:
            d.get(self.url_consulta)
            self._campo_visivel()
            return

        item = self._achar(SELETOR_MENU)[0]
        href = item.get_attribute("href")  # endereço completo (com o hash da sessão)
        try:
            if not item.is_displayed():
                pai = self._achar(SELETOR_MENU_PAI) or d.find_elements(
                    By.XPATH, "//a[normalize-space()='Consulta Processual']")
                pai[0].click()
                self._esperar(lambda _: item.is_displayed(), 10)
            item.click()
            try:
                self._campo_visivel(8)
            except Exception:
                # O "Consultar Processos" abriu um submenu: clica no de dentro dele.
                alvo = item.get_attribute("data-target")
                sub = [a for a in self._achar(f"{alvo} a") if "Consultar Processos" in a.text]
                sub[0].click()
                self._campo_visivel()
        except Exception as e:
            print(f"Não consegui pelo menu ({type(e).__name__}); abrindo a tela de consulta direto.")
            d.get(href)
            self._campo_visivel()
        self.url_consulta = d.current_url

    def abrir_processo(self, numero: str):
        self.abrir_consulta()
        campo = self._campo_visivel()
        campo.clear()
        campo.send_keys(numero)
        self._achar(SELETOR_BOTAO)[0].click()
        try:
            self._esperar(lambda _: self._achar(SELETOR_EVENTO) or self._achar(SELETOR_LINK_PROCESSO))
        except Exception:
            raise RuntimeError("processo não encontrado (a consulta não mostrou o processo nem uma "
                               "lista de resultados). Confira o número.") from None
        if not self._achar(SELETOR_EVENTO):
            # Caiu numa lista de resultados: abre o processo com o mesmo número.
            links = self._achar(SELETOR_LINK_PROCESSO)
            alvo = next((a for a in links if so_digitos(numero) and so_digitos(numero) in so_digitos(a.text)),
                        links[0])
            alvo.click()
            self._esperar(lambda _: self._achar(SELETOR_EVENTO))

    def ler_eventos(self) -> list[dict]:
        return montar_eventos(self.driver.execute_script(f"return ({JS_EVENTOS})();"))

    def baixar(self, url: str) -> tuple[bytes, str]:
        resultado = self.driver.execute_async_script(
            f"const fim = arguments[arguments.length - 1];"
            f"({JS_BAIXAR})(arguments[0]).then(fim, e => fim({{erro: String(e)}}));", url)
        return resultado_download(resultado)


# ---------------------------------------------------------------------------
# Texto dos documentos
# ---------------------------------------------------------------------------

class TextoHTML(HTMLParser):
    """Tira o texto de uma página HTML e anota os iframes/embeds (onde o documento pode estar)."""

    IGNORAR = {"script", "style", "head", "title"}
    BLOCOS = {"p", "div", "br", "tr", "li", "h1", "h2", "h3", "h4", "table", "section"}

    def __init__(self):
        super().__init__()
        self.partes: list[str] = []
        self.quadros: list[str] = []
        self._ignorando = 0

    def handle_starttag(self, tag, attrs):
        if tag in self.IGNORAR:
            self._ignorando += 1
        if tag in self.BLOCOS:
            self.partes.append("\n")
        if tag in ("iframe", "embed", "frame", "object"):
            a = dict(attrs)
            src = a.get("src") or a.get("data")
            if src and not src.startswith(("about:", "javascript:")):
                self.quadros.append(src)

    def handle_endtag(self, tag):
        if tag in self.IGNORAR and self._ignorando:
            self._ignorando -= 1

    def handle_data(self, data):
        if not self._ignorando:
            self.partes.append(data)

    def texto(self) -> str:
        texto = "".join(self.partes)
        texto = re.sub(r"[ \t\xa0]+", " ", texto)
        return re.sub(r"\n\s*\n+", "\n\n", texto).strip()


def decodificar(conteudo: bytes, tipo: str) -> str:
    m = re.search(r"charset=([\w-]+)", tipo, re.I)
    for cod in ([m.group(1)] if m else []) + ["utf-8", "latin-1"]:
        try:
            return conteudo.decode(cod)
        except (UnicodeDecodeError, LookupError):
            pass
    return conteudo.decode("latin-1", errors="replace")


def texto_pdf(conteudo: bytes) -> str:
    import pymupdf  # PyMuPDF, o mesmo dos outros scripts
    with pymupdf.open(stream=conteudo, filetype="pdf") as pdf:
        texto = "\n".join(pagina.get_text() for pagina in pdf).strip()
    return texto or "(PDF sem texto: provavelmente é digitalizado/imagem. Veja o arquivo salvo.)"


def nome_arquivo(texto: str) -> str:
    return re.sub(r"[^\w.-]+", "_", texto).strip("_")[:80] or "documento"


def ler_documento(robo: Robo, url: str, destino_sem_ext: Path, profundidade: int = 0) -> tuple[str, Path]:
    """Baixa o documento, salva uma cópia e devolve (texto, arquivo salvo). Se a página só embrulha
    o documento num iframe, segue o iframe."""
    conteudo, tipo = robo.baixar(url)
    if conteudo[:4] == b"%PDF" or "pdf" in tipo.lower():
        arquivo = destino_sem_ext.with_suffix(".pdf")
        arquivo.write_bytes(conteudo)
        return texto_pdf(conteudo), arquivo

    if "html" in tipo.lower() or conteudo.lstrip()[:1] == b"<":
        html = decodificar(conteudo, tipo)
        leitor = TextoHTML()
        leitor.feed(html)
        texto = leitor.texto()
        if leitor.quadros and profundidade < 2 and len(texto) < 300:
            return ler_documento(robo, urljoin(url, leitor.quadros[0]), destino_sem_ext, profundidade + 1)
        arquivo = destino_sem_ext.with_suffix(".html")
        arquivo.write_bytes(conteudo)
        return texto, arquivo

    extensao = {"image/jpeg": ".jpg", "image/png": ".png"}.get(tipo.split(";")[0].strip(), ".bin")
    arquivo = destino_sem_ext.with_suffix(extensao)
    arquivo.write_bytes(conteudo)
    return f"(Arquivo do tipo '{tipo or 'desconhecido'}': sem texto. Veja o arquivo salvo.)", arquivo



# ---------------------------------------------------------------------------
# Estado
# ---------------------------------------------------------------------------

def carregar_estado() -> dict:
    if not ARQUIVO_ESTADO.exists():
        return {}
    try:
        return json.loads(ARQUIVO_ESTADO.read_text(encoding="utf-8"))
    except Exception as e:
        raise SystemExit(f"Não consegui ler {ARQUIVO_ESTADO} ({e}). Restaure uma cópia; não apague, "
                         f"senão o robô esquece o que já foi visto.")


def salvar_estado(estado: dict):
    ARQUIVO_ESTADO.parent.mkdir(parents=True, exist_ok=True)
    temporario = ARQUIVO_ESTADO.with_suffix(".tmp")
    temporario.write_text(json.dumps(estado, ensure_ascii=False, indent=2), encoding="utf-8")
    temporario.replace(ARQUIVO_ESTADO)


def recortar(texto: str) -> str:
    if LIMITE_TEXTO and len(texto) > LIMITE_TEXTO:
        return texto[:LIMITE_TEXTO] + f"\n[... texto cortado em {LIMITE_TEXTO} caracteres; veja o arquivo]"
    return texto


def recuar(texto: str, espacos: int) -> str:
    return "\n".join(" " * espacos + linha for linha in texto.splitlines())


def rotulo_doc(doc: dict) -> str:
    rotulo = doc["nome"] or "documento"
    if doc["titulo"] and doc["titulo"] != rotulo:
        rotulo += f" ({doc['titulo']})"
    return rotulo


def titulo_evento(evento: dict) -> str:
    parte = f" - parte: {evento['parte']}" if evento["parte"] else ""
    return f"Evento {evento['numero']} - {evento['data']}{parte}"


# ---------------------------------------------------------------------------
# Consulta de um processo
# ---------------------------------------------------------------------------

def ler_documentos_evento(robo, numero: str, evento: dict):
    """Abre os documentos do evento, salva uma cópia e guarda o texto em evento['lidos']."""
    pasta = PASTA_DOCUMENTOS / nome_arquivo(numero)
    evento["lidos"] = []
    for doc in evento["docs"]:
        lido = {"rotulo": rotulo_doc(doc), "texto": "", "arquivo": None, "erro": None, "link": None}
        try:
            pasta.mkdir(parents=True, exist_ok=True)
            lido["texto"], lido["arquivo"] = ler_documento(
                robo, doc["href"], pasta / nome_arquivo(f"evento{evento['numero']}_{doc['nome']}"))
        except Exception as e:
            lido["erro"] = erro_curto(e)
            print(f"  ERRO no documento {lido['rotulo']} do evento {evento['numero']}: {lido['erro']}")
        evento["lidos"].append(lido)


def acompanhar(robo, numero: str, estado: dict, ler_ultimo: bool = False) -> dict:
    """Consulta um processo e lê os documentos dos eventos novos. NÃO grava o estado: quem chama
    grava depois que o Google Doc for atualizado (se o Google falhar, a próxima vez tenta de novo).
    ler_ultimo: lê também os documentos do último evento mesmo sem mudança (para criar o Doc)."""
    robo.abrir_processo(numero)
    eventos = robo.ler_eventos()
    if not eventos:
        raise RuntimeError("não encontrei a tabela de eventos")

    anterior = estado.get(numero, {}).get("ultimo_evento")
    if anterior is None:
        situacao = "primeira"
        novos = eventos[-PRIMEIRA_VEZ_EVENTOS:] if PRIMEIRA_VEZ_EVENTOS else []
    else:
        novos = [e for e in eventos if e["numero"] > anterior]
        situacao = "novos" if novos else "sem_mudanca"

    for evento in novos:
        ler_documentos_evento(robo, numero, evento)
    if ler_ultimo and not novos:
        ler_documentos_evento(robo, numero, eventos[-1])

    return {"numero": numero, "situacao": situacao, "anterior": anterior,
            "atual": eventos[-1]["numero"], "eventos": eventos, "novos": novos}


def resumo(r: dict) -> str:
    numero = r["numero"]
    if r["situacao"] == "erro":
        return f"PROCESSO {numero}: {r['mensagem']}"
    if r["situacao"] == "primeira":
        return (f"PROCESSO {numero}: primeira consulta (último evento: {r['atual']}). "
                f"Mostrando os {len(r['novos'])} último(s).")
    if r["situacao"] == "sem_mudanca":
        return f"PROCESSO {numero}: sem mudanças (último evento: {r['atual']})."
    return (f"PROCESSO {numero}: {len(r['novos'])} evento(s) novo(s) "
            f"(antes: {r['anterior']}, agora: {r['atual']}).")


def linhas_relatorio(r: dict) -> list[str]:
    """Relatório em texto (cópia local, em relatorios/)."""
    linhas = [resumo(r)]
    if r.get("link_doc"):
        linhas.append(f"  Google Doc: {r['link_doc']}")
    if r.get("link_pasta"):
        linhas.append(f"  Pasta no Drive: {r['link_pasta']}")
    if r.get("erro_google"):
        linhas.append(f"  ERRO no Google: {r['erro_google']} (vai ser tentado de novo na próxima vez)")
    for evento in sorted(r.get("novos", []), key=lambda e: e["numero"], reverse=True):
        linhas += ["", "  " + titulo_evento(evento), recuar(evento["descricao"], 4)]
        for lido in evento["lidos"]:
            linhas += ["", f"    >> Documento {lido['rotulo']}"]
            if lido["erro"]:
                linhas.append(f"       ERRO ao abrir o documento: {lido['erro']}")
                continue
            linhas.append(f"       Arquivo: {lido['arquivo']}")
            if lido["link"]:
                linhas.append(f"       No Drive: {lido['link']}")
            linhas.append(recuar(recortar(lido["texto"]), 7))
    return linhas


# ---------------------------------------------------------------------------
# Google (Docs, Drive e Gmail)
# ---------------------------------------------------------------------------

# drive.file: o robô só enxerga os arquivos que ele mesmo criou (não lê o resto do seu Drive).
ESCOPOS_GOOGLE = ["https://www.googleapis.com/auth/drive.file",
                  "https://www.googleapis.com/auth/gmail.send"]
TIPO_DOC = "application/vnd.google-apps.document"
TIPO_PASTA = "application/vnd.google-apps.folder"
MARCADOR_EVENTOS = "Eventos (mais recentes primeiro)"

INSTRUCOES_GOOGLE = """
Falta o arquivo de acesso ao Google: {arquivo}

Como criar (uma vez só, logado na conta Google que vai mandar os e-mails e guardar os Docs):
  1. Entre em https://console.cloud.google.com e crie um projeto (ex.: "Robo eproc").
  2. Em "APIs e serviços" > "Biblioteca", ative: Google Drive API, Google Docs API e Gmail API.
  3. Em "APIs e serviços" > "Tela de consentimento OAuth": tipo Externo, preencha o nome do app e o
     seu e-mail, e em "Usuários de teste" adicione a conta Google que vai ser usada.
  4. Em "APIs e serviços" > "Credenciais" > "Criar credenciais" > "ID do cliente OAuth",
     tipo "App para computador". Baixe o JSON.
  5. Salve o JSON nesta pasta (pode manter o nome client_secret_....json): {pasta}
  6. Rode o robô de novo. O navegador abre: entre com a conta que vai MANDAR os e-mails e autorize.

Para rodar sem o Google (só o relatório .txt), ponha USAR_GOOGLE = False no começo do arquivo.
"""


def credenciais_google():
    from google.auth.transport.requests import Request
    from google.oauth2.credentials import Credentials
    from google_auth_oauthlib.flow import InstalledAppFlow

    arquivo_token = PASTA_GOOGLE / "token.json"
    arquivo_cliente = PASTA_GOOGLE / "credentials.json"
    if not arquivo_cliente.exists():
        # Aceita também o nome com que o Google baixa o arquivo (client_secret_....json).
        baixados = sorted(PASTA_GOOGLE.glob("client_secret*.json"))
        if baixados:
            arquivo_cliente = baixados[-1]
    creds = None
    if arquivo_token.exists():
        creds = Credentials.from_authorized_user_file(str(arquivo_token), ESCOPOS_GOOGLE)
    if creds and creds.valid:
        return creds
    if creds and creds.expired and creds.refresh_token:
        try:
            creds.refresh(Request())
            arquivo_token.write_text(creds.to_json(), encoding="utf-8")
            return creds
        except Exception:
            print("A autorização do Google expirou; é preciso entrar na conta de novo.")
    if not arquivo_cliente.exists():
        PASTA_GOOGLE.mkdir(parents=True, exist_ok=True)
        raise SystemExit(INSTRUCOES_GOOGLE.format(arquivo=arquivo_cliente, pasta=PASTA_GOOGLE))
    print("Abrindo o navegador para você entrar na conta Google e autorizar o robô...")
    fluxo = InstalledAppFlow.from_client_secrets_file(str(arquivo_cliente), ESCOPOS_GOOGLE)
    creds = fluxo.run_local_server(port=0, prompt="consent")
    PASTA_GOOGLE.mkdir(parents=True, exist_ok=True)
    arquivo_token.write_text(creds.to_json(), encoding="utf-8")
    return creds


def tamanho_docs(texto: str) -> int:
    """O Google Docs conta posições em unidades UTF-16 (um emoji vale 2)."""
    return len(texto.encode("utf-16-le")) // 2


def limpar_docs(texto: str) -> str:
    """Tira caracteres de controle que o Google Docs recusa; cada bloco vira uma linha só."""
    texto = texto.replace("\r\n", " ").replace("\r", " ").replace("\n", " ")
    return re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f\x7f￾￿]", "", texto)


def requisicoes_insercao(indice: int, blocos: list[tuple[str, str, str | None]],
                         quebra_antes: bool = False) -> list[dict]:
    """Pedidos ao Google Docs para inserir os blocos (texto, estilo, link) a partir de `indice`.
    Cada bloco vira um parágrafo com o estilo dado (TITLE, HEADING_1, NORMAL_TEXT...)."""
    blocos = [(limpar_docs(t), estilo, link) for t, estilo, link in blocos]
    texto = ("\n" if quebra_antes else "") + "".join(t + "\n" for t, _, _ in blocos)
    pedidos = [
        {"insertText": {"location": {"index": indice}, "text": texto}},
        # O texto inserido herdaria o estilo do vizinho (negrito, link...): zera.
        {"updateTextStyle": {"range": {"startIndex": indice, "endIndex": indice + tamanho_docs(texto)},
                             "textStyle": {}, "fields": "bold,italic,underline,link"}},
    ]
    pos = indice + (1 if quebra_antes else 0)
    for t, estilo, link in blocos:
        fim = pos + tamanho_docs(t) + 1
        pedidos.append({"updateParagraphStyle": {"range": {"startIndex": pos, "endIndex": fim},
                                                 "paragraphStyle": {"namedStyleType": estilo},
                                                 "fields": "namedStyleType"}})
        if link and t:
            pedidos.append({"updateTextStyle": {"range": {"startIndex": pos, "endIndex": fim - 1},
                                                "textStyle": {"link": {"url": link}}, "fields": "link"}})
        pos = fim
    return pedidos


def blocos_evento(evento: dict) -> list[tuple[str, str, str | None]]:
    blocos = [(titulo_evento(evento), "HEADING_2", None)]
    blocos += [(linha, "NORMAL_TEXT", None) for linha in evento["descricao"].splitlines() if linha.strip()]
    if "lidos" in evento:
        for lido in evento["lidos"]:
            blocos.append((f"Documento {lido['rotulo']}", "HEADING_3", lido["link"]))
            if lido["erro"]:
                blocos.append((f"Erro ao abrir o documento: {lido['erro']}", "NORMAL_TEXT", None))
            else:
                blocos += [(linha, "NORMAL_TEXT", None) for linha in recortar(lido["texto"]).splitlines()]
    elif evento["docs"]:
        # Eventos antigos (primeira vez): só os nomes dos documentos, sem abrir.
        blocos.append(("Documentos: " + ", ".join(rotulo_doc(d) for d in evento["docs"]), "NORMAL_TEXT", None))
    blocos.append(("", "NORMAL_TEXT", None))
    return blocos


def link_doc(doc_id: str) -> str:
    return f"https://docs.google.com/document/d/{doc_id}/edit"


def link_pasta(pasta_id: str | None) -> str | None:
    return f"https://drive.google.com/drive/folders/{pasta_id}" if pasta_id else None


class Google:
    def __init__(self, drive=None, docs=None, gmail=None):
        if drive is None:
            from googleapiclient.discovery import build
            creds = credenciais_google()
            drive = build("drive", "v3", credentials=creds, cache_discovery=False)
            docs = build("docs", "v1", credentials=creds, cache_discovery=False)
            gmail = build("gmail", "v1", credentials=creds, cache_discovery=False)
        self.drive, self.docs, self.gmail = drive, docs, gmail

    def existe(self, arquivo_id: str | None) -> bool:
        if not arquivo_id:
            return False
        try:
            return not self.drive.files().get(fileId=arquivo_id, fields="trashed").execute().get("trashed")
        except Exception as e:
            if getattr(getattr(e, "resp", None), "status", None) in (403, 404):
                return False  # apagado, ou não é mais acessível
            raise

    def pasta(self, nome: str, pai: str | None = None) -> str:
        """Id da pasta com esse nome (cria se não existir)."""
        nome_q = nome.replace("\\", "\\\\").replace("'", "\\'")
        q = f"mimeType='{TIPO_PASTA}' and name='{nome_q}' and trashed=false"
        if pai:
            q += f" and '{pai}' in parents"
        achadas = self.drive.files().list(q=q, fields="files(id)", pageSize=1).execute().get("files", [])
        if achadas:
            return achadas[0]["id"]
        corpo = {"name": nome, "mimeType": TIPO_PASTA}
        if pai:
            corpo["parents"] = [pai]
        return self.drive.files().create(body=corpo, fields="id").execute()["id"]

    def mover(self, arquivo_id: str, pasta_id: str):
        """Põe o arquivo dentro da pasta (se ainda não estiver)."""
        pais = self.drive.files().get(fileId=arquivo_id, fields="parents").execute().get("parents", [])
        if pasta_id not in pais:
            self.drive.files().update(fileId=arquivo_id, addParents=pasta_id,
                                      removeParents=",".join(pais), fields="id").execute()

    def criar_doc(self, titulo: str, pasta_id: str) -> str:
        doc_id = self.drive.files().create(
            body={"name": titulo, "mimeType": TIPO_DOC, "parents": [pasta_id]}, fields="id").execute()["id"]
        cabecalho = [(titulo, "TITLE", None),
                     ("Acompanhamento automático do eproc (TJRJ). Cada evento novo entra logo abaixo, "
                      "o mais recente primeiro. O que você escrever aqui é mantido.", "NORMAL_TEXT", None),
                     (MARCADOR_EVENTOS, "HEADING_1", None)]
        self.docs.documents().batchUpdate(
            documentId=doc_id, body={"requests": requisicoes_insercao(1, cabecalho)}).execute()
        return doc_id

    def ponto_de_insercao(self, doc_id: str) -> tuple[int, bool]:
        """Logo abaixo do título 'Eventos (mais recentes primeiro)'. Se ele foi apagado, no fim."""
        doc = self.docs.documents().get(documentId=doc_id).execute()
        conteudo = doc["body"]["content"]
        for i, el in enumerate(conteudo):
            par = el.get("paragraph")
            if not par:
                continue
            texto = "".join(e.get("textRun", {}).get("content", "") for e in par.get("elements", []))
            if texto.strip() == MARCADOR_EVENTOS and i < len(conteudo) - 1:
                return el["endIndex"], False
        return conteudo[-1]["endIndex"] - 1, True

    def inserir(self, doc_id: str, blocos):
        indice, quebra = self.ponto_de_insercao(doc_id)
        self.docs.documents().batchUpdate(
            documentId=doc_id, body={"requests": requisicoes_insercao(indice, blocos, quebra)}).execute()

    def subir(self, caminho: Path, pasta_id: str) -> str:
        import mimetypes
        from googleapiclient.http import MediaFileUpload
        tipo = mimetypes.guess_type(caminho.name)[0] or "application/octet-stream"
        arquivo = self.drive.files().create(
            body={"name": caminho.name, "parents": [pasta_id]},
            media_body=MediaFileUpload(str(caminho), mimetype=tipo, resumable=False),
            fields="id,webViewLink").execute()
        return arquivo["webViewLink"]

    def enviar_email(self, destinos: list[str], assunto: str, html: str):
        from email.message import EmailMessage
        msg = EmailMessage()
        msg["To"] = ", ".join(destinos)
        msg["Subject"] = assunto
        msg.set_content("Este e-mail tem a versão completa em HTML.")
        msg.add_alternative(html, subtype="html")
        bruto = base64.urlsafe_b64encode(msg.as_bytes()).decode()
        self.gmail.users().messages().send(userId="me", body={"raw": bruto}).execute()


def preparar_pasta_raiz(google: Google, estado: dict) -> str:
    g = estado.setdefault("__google__", {})
    if not google.existe(g.get("pasta")):
        g["pasta"] = google.pasta(NOME_PASTA_DRIVE)
    return g["pasta"]


def sincronizar_google(google: Google, r: dict, estado: dict, pasta_raiz: str) -> dict:
    """Atualiza a pasta do processo no Drive ("Processo <número>", dentro de NOME_PASTA_DRIVE):
      - o Google Doc do processo: criado na 1ª vez só com o último evento; depois, cada evento novo
        é acrescentado no mesmo Doc;
      - os documentos dos eventos novos, salvos na mesma pasta.
    Devolve o que deve ir para o estado do processo."""
    numero = r["numero"]
    proc = estado.get(numero, {})
    doc_id = proc.get("doc_id")
    pasta = proc.get("pasta_processo")
    if r["situacao"] == "sem_mudanca" and pasta and google.existe(doc_id):
        return {"doc_id": doc_id, "link_doc": link_doc(doc_id),  # nada a fazer
                "pasta_processo": pasta, "link_pasta": link_pasta(pasta)}

    if not google.existe(pasta):
        pasta = google.pasta(f"Processo {numero}", pasta_raiz)

    if google.existe(doc_id):
        google.mover(doc_id, pasta)  # Doc de versão antiga, solto na pasta principal
        eventos_doc = r["novos"]
    else:
        doc_id = google.criar_doc(f"Processo {numero}", pasta)
        # Doc novo: só o último evento (ou os eventos novos, se já houver), não o histórico todo.
        eventos_doc = r["novos"] or r["eventos"][-1:]

    lidos = [l for e in eventos_doc for l in e.get("lidos", []) if l["arquivo"]]
    # Arquivos já enviados (se o Google falhou no meio da vez anterior, não sobe de novo).
    enviados = estado.setdefault("__google__", {}).setdefault("enviados", {})
    for lido in lidos:
        chave = str(lido["arquivo"])
        if chave not in enviados:
            enviados[chave] = google.subir(Path(lido["arquivo"]), pasta)
            salvar_estado(estado)
        lido["link"] = enviados[chave]

    blocos = []
    for evento in sorted(eventos_doc, key=lambda e: e["numero"], reverse=True):
        blocos += blocos_evento(evento)
    if blocos:
        google.inserir(doc_id, blocos)
    return {"doc_id": doc_id, "link_doc": link_doc(doc_id),
            "pasta_processo": pasta, "link_pasta": link_pasta(pasta)}


def montar_email(resultados: list[dict]) -> tuple[str, str] | None:
    """(assunto, html) do e-mail. Com EMAIL_SEMPRE, sai mesmo sem mudanças (com o resumo de cada
    processo); sem ele, None se nada mudou."""
    from html import escape

    def paragrafos(texto: str) -> str:
        return escape(texto).replace("\n", "<br>")

    def links(r: dict) -> str:
        saida = ""
        if r.get("link_doc"):
            saida += f" &middot; <a href='{escape(r['link_doc'])}'>Google Doc</a>"
        if r.get("link_pasta"):
            saida += f" &middot; <a href='{escape(r['link_pasta'])}'>pasta no Drive</a>"
        return saida

    mudaram = [r for r in resultados if not r.get("erro_google") and
               (r["situacao"] == "novos" or (EMAIL_NA_PRIMEIRA_VEZ and r["situacao"] == "primeira"))]
    sem_mudanca = [r for r in resultados if not r.get("erro_google") and r not in mudaram
                   and r["situacao"] in ("sem_mudanca", "primeira")]
    if not mudaram and not (EMAIL_SEMPRE and resultados):
        return None
    data = f"{datetime.now():%d/%m/%Y %H:%M}"
    if mudaram:
        total = sum(len(r["novos"]) for r in mudaram)
        assunto = f"eproc: {total} evento(s) novo(s) em {len(mudaram)} processo(s) - {data}"
        abertura = f"Movimentações novas encontradas no eproc em {agora()}."
    else:
        assunto = f"eproc: sem movimentações novas - {data}"
        abertura = (f"Consulta feita no eproc em {agora()}: nenhum dos {len(resultados)} processo(s) "
                    f"teve movimentação nova.")
    partes = ["<div style='font-family:Arial,sans-serif;font-size:14px;color:#222'>",
              f"<p>{escape(abertura)}</p>"]
    for r in mudaram:
        partes.append(f"<h2 style='margin-top:28px;border-bottom:1px solid #ccc'>Processo {escape(r['numero'])}</h2>")
        partes.append(f"<p>{escape(resumo(r).split(': ', 1)[1])}")
        if r.get("link_doc"):
            partes.append(f" &middot; <a href='{escape(r['link_doc'])}'>Abrir o Google Doc do processo</a>")
        if r.get("link_pasta"):
            partes.append(f" &middot; <a href='{escape(r['link_pasta'])}'>Abrir a pasta do processo</a>")
        partes.append("</p>")
        for evento in sorted(r["novos"], key=lambda e: e["numero"], reverse=True):
            partes.append(f"<h3 style='margin-bottom:4px'>{escape(titulo_evento(evento))}</h3>")
            partes.append(f"<p style='margin-top:0'>{paragrafos(evento['descricao'])}</p>")
            for lido in evento["lidos"]:
                link = f" (<a href='{escape(lido['link'])}'>abrir no Drive</a>)" if lido["link"] else ""
                partes.append(f"<p><b>Documento {escape(lido['rotulo'])}</b>{link}</p>")
                if lido["erro"]:
                    partes.append(f"<p style='color:#b00'>Erro ao abrir o documento: {escape(lido['erro'])}</p>")
                else:
                    partes.append("<div style='white-space:pre-wrap;border-left:3px solid #ccc;"
                                  f"padding-left:10px;color:#333'>{escape(recortar(lido['texto']))}</div>")
    if sem_mudanca:
        partes.append("<h3 style='margin-top:28px'>Processos sem movimentação nova</h3><ul>")
        for r in sem_mudanca:
            ultimo = r["eventos"][-1]
            partes.append(f"<li><b>{escape(r['numero'])}</b>: último evento {ultimo['numero']} "
                          f"({escape(ultimo['data'])}) - {escape(ultimo['descricao'].splitlines()[0] if ultimo['descricao'] else '')}"
                          f"{links(r)}</li>")
        partes.append("</ul>")
    erros = [r for r in resultados if r["situacao"] == "erro" or r.get("erro_google")]
    if erros:
        partes.append("<h3 style='color:#b00'>Processos que deram erro</h3><ul>")
        partes += [f"<li>{escape(r['numero'])}: {escape(r.get('mensagem') or 'Google: ' + r['erro_google'])}</li>"
                   for r in erros]
        partes.append("</ul>")
    partes.append("</div>")
    return assunto, "".join(partes)


# ---------------------------------------------------------------------------
# Execução
# ---------------------------------------------------------------------------

def pedir_processos() -> list[str]:
    print("\nDigite ou cole os números dos processos (linha vazia termina):")
    numeros: list[str] = []
    while True:
        linha = input("> ").strip()
        if not linha:
            break
        for parte in re.split(r"[,;\s]+", linha):
            if parte and parte not in numeros:
                numeros.append(parte)
    return numeros


def consultar_todos(robo, numeros: list[str], estado: dict, google: Google | None) -> list[dict]:
    pasta_raiz = None
    resultados = []
    for i, numero in enumerate(numeros, 1):
        print(f"[{i}/{len(numeros)}] {numero}")
        try:
            # Se o Doc do processo ainda não existe (ou foi para a lixeira), ele vai ser criado com o
            # último evento: então lê os documentos desse evento mesmo sem mudança.
            ler_ultimo = False
            if google and USAR_GOOGLE_DOCS:
                try:
                    ler_ultimo = not google.existe(estado.get(numero, {}).get("doc_id"))
                except Exception:
                    ler_ultimo = True
            r = acompanhar(robo, numero, estado, ler_ultimo)
        except Exception as e:
            r = {"numero": numero, "situacao": "erro", "mensagem": f"ERRO na consulta: {erro_curto(e)}"}
            print(f"  ERRO: {erro_curto(e)}")
            resultados.append(r)
            continue

        novo = dict(estado.get(numero, {}))
        novo.update(ultimo_evento=r["atual"], consultado=agora())
        if google and USAR_GOOGLE_DOCS:
            try:
                pasta_raiz = pasta_raiz or preparar_pasta_raiz(google, estado)
                novo.update(sincronizar_google(google, r, estado, pasta_raiz))
                r["link_doc"] = novo["link_doc"]
                r["link_pasta"] = novo.get("link_pasta")
            except Exception as e:
                # Não grava o estado: na próxima vez o robô vê estes eventos como novos de novo.
                r["erro_google"] = erro_curto(e)
                print(f"  ERRO no Google: {r['erro_google']} (vai ser tentado de novo na próxima vez)")
                resultados.append(r)
                continue
        estado[numero] = novo
        salvar_estado(estado)  # a cada processo, para não perder nada se cair
        print("  " + resumo(r))
        resultados.append(r)
    return resultados


def rodar_chrome(numeros, estado, google):
    from playwright.sync_api import sync_playwright

    abrir_chrome()
    with sync_playwright() as p:
        browser = p.chromium.connect_over_cdp(endereco_chrome())
        try:
            page = esperar_login(browser.contexts[0])
            page.bring_to_front()
            page.set_default_timeout(ESPERA_MS)
            return consultar_todos(Robo(page), numeros, estado, google)
        finally:
            try:
                browser.close()  # só desconecta; o Chrome continua aberto
            except Exception:
                pass


def rodar_firefox(numeros, estado, google):
    abrir_firefox()
    driver = conectar_firefox()
    try:
        esperar_login_firefox(driver)
        return consultar_todos(RoboFirefox(driver), numeros, estado, google)
    finally:
        # Só desliga o robô (geckodriver). O Firefox continua aberto.
        try:
            driver.service.stop()
        except Exception:
            pass


def conectar_google() -> Google | None:
    if not USAR_GOOGLE:
        return None
    try:
        import googleapiclient  # noqa: F401
        import google_auth_oauthlib  # noqa: F401
    except ImportError:
        raise SystemExit("Faltam as bibliotecas do Google. Rode:\n"
                         "  pip install google-api-python-client google-auth-oauthlib\n"
                         "(ou ponha USAR_GOOGLE = False para rodar sem o Google)")
    google = Google()
    print("Conta Google conectada.")
    if not EMAIL_DESTINO:
        print("AVISO: EMAIL_DESTINO está vazio no começo do arquivo; o e-mail não vai ser enviado.")
    return google


def enviar_email_mudancas(google: Google | None, resultados: list[dict]):
    email = montar_email(resultados)
    if not email:
        print("Nenhuma movimentação nova: e-mail não enviado (EMAIL_SEMPRE = False).")
        return
    assunto, html = email
    PASTA_RELATORIOS.mkdir(parents=True, exist_ok=True)
    copia = PASTA_RELATORIOS / f"email_{datetime.now():%Y-%m-%d_%H%M%S}.html"
    copia.write_text(html, encoding="utf-8")  # cópia do e-mail, para conferir
    if not google or not EMAIL_DESTINO:
        print(f"E-mail não enviado (sem Google ou sem EMAIL_DESTINO). Cópia em: {copia}")
        return
    try:
        google.enviar_email(EMAIL_DESTINO, assunto, html)
        print(f"E-mail enviado para {', '.join(EMAIL_DESTINO)}.")
    except Exception as e:
        print(f"ERRO ao enviar o e-mail: {erro_curto(e)}. Cópia em: {copia}")


def main():
    numeros = pedir_processos()
    if not numeros:
        print("Nenhum processo digitado.")
        return
    estado = carregar_estado()
    google = conectar_google()  # antes do eproc: se faltar algo do Google, avisa logo

    inicio = agora()
    if NAVEGADOR == "firefox":
        resultados = rodar_firefox(numeros, estado, google)
    else:
        resultados = rodar_chrome(numeros, estado, google)

    relatorio = [f"RELATÓRIO eproc - {inicio}", "=" * 70]
    for r in resultados:
        relatorio += linhas_relatorio(r) + ["", "-" * 70]
    erros = [r["numero"] for r in resultados if r["situacao"] == "erro" or r.get("erro_google")]
    if erros:
        relatorio.append("Processos com erro (rode de novo só com eles): " + ", ".join(erros))
    PASTA_RELATORIOS.mkdir(parents=True, exist_ok=True)
    arquivo = PASTA_RELATORIOS / f"relatorio_{datetime.now():%Y-%m-%d_%H%M%S}.txt"
    arquivo.write_text("\n".join(relatorio) + "\n", encoding="utf-8")
    print(f"\nRelatório salvo em: {arquivo}")

    enviar_email_mudancas(google, resultados)
    if not google or not USAR_GOOGLE_DOCS:
        try:
            os.startfile(arquivo)  # sem o Google Doc, abre o relatório no Bloco de Notas
        except Exception:
            pass


if __name__ == "__main__":
    main()
