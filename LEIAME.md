# Radar de artigos — versão SITE

Um site que se atualiza sozinho todo dia com artigos novos sobre os seus temas
e uma aba de clássicos (os mais citados). Você manda o link para quem quiser.

## Passo a passo (sem precisar saber programar)

1. Crie uma conta grátis em github.com.
2. Clique em "+" (canto superior direito) > "New repository".
   - Nome: radar-abelhas (ou outro)
   - Marque **Public** (precisa ser público para o site grátis funcionar)
   - Clique em "Create repository".
3. Na página do repositório novo, clique em "uploading an existing file".
   Arraste TODO o conteúdo da pasta radar-artigos (inclusive a pasta ".github"
   e o arquivo config.yaml). Clique em "Commit changes".
   Dica: se a pasta .github não subir pelo navegador, use o GitHub Desktop
   (desktop.github.com), que envia tudo certinho.
4. Ative o site: Settings > Pages > em "Branch" escolha **main** e a pasta
   **/docs** > Save.
5. Rode a primeira vez: aba Actions > "Radar de artigos" > "Run workflow".
   (Se aparecer um botão pedindo para habilitar workflows, habilite.)
6. Espere uns 2 minutos. O endereço do seu site fica em Settings > Pages, algo como
   https://SEU-USUARIO.github.io/radar-abelhas/
7. Pronto: ele se atualiza sozinho todo dia às 7h (Brasília).

## Como mudar os temas
Abra config.yaml no GitHub (ícone de lápis), edite os termos e salve.
Evite vírgulas dentro dos termos.

## Como ficam as coisas
- Aba "Novidades": artigos novos, agrupados pelo dia em que chegaram.
- Aba "Clássicos": os mais citados de cada tema, ordenados por citações.
- Busca por palavra e filtro por tema.
- E-mail é opcional (config.yaml > email > ativo).

## Testar no seu computador (opcional)
    pip install -r requirements.txt
    python radar_artigos.py diario
    # abra docs/index.html no navegador
