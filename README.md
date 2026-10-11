# Simulador — Força de Lorentz

Simulação 3D interativa do movimento de partículas carregadas em um campo magnético. A ideia é dar vida a uma equação que normalmente só aparece no quadro:

**F = q(v × B)**

Demo: https://simulador-forca-lorentz.vercel.app

## Sobre o projeto

Esse é um projeto acadêmico sobre a Força de Lorentz. Em vez de só mostrar a fórmula, a proposta foi deixar a pessoa mexer nos parâmetros — campo, carga, velocidade — e ver na hora como a trajetória muda: círculo quando a velocidade é perpendicular ao campo, hélice quando tem uma componente paralela.

A simulação roda com um integrador de Boris (que mantém o módulo da velocidade constante, já que a força magnética não realiza trabalho) e leva em conta efeitos relativísticos através do fator de Lorentz (γ), então os valores continuam corretos mesmo perto da velocidade da luz.

Também tem uma tabela que compara os valores teóricos (fórmulas fechadas de raio, período e energia cinética) com o que a simulação mede de fato, pra mostrar que o integrador está certo e não é só uma animação bonita.

## O que dá pra fazer

- Escolher elétron ou próton (carga e massa reais, não inventadas)
- Ajustar o campo B e a velocidade inicial livremente, ou carregar um cenário pronto
- Girar a câmera em 3D, com atalhos pra vista XY, XZ, YZ ou um botão que alinha a câmera com o próprio campo B (nesse caso o campo aparece com os símbolos ⊗/⊙, já que uma seta apontando direto pra câmera não dá pra desenhar)
- Ver os vetores de v e F, a trajetória, linhas de campo e um disco marcando o raio da órbita
- Controlar o ritmo da simulação (de 0,25× a 4×) ou avançar passo a passo
- Acompanhar gráficos de velocidade e das grandezas conservadas
- Exportar imagem, vídeo ou o CSV da trajetória, e copiar um link do cenário atual pra compartilhar
- Tema claro/escuro, tela cheia, tutorial na primeira visita

### Atalhos de teclado

| Tecla | Ação |
|---|---|
| Espaço | inicia/pausa |
| . | avança um passo |
| R | reseta |
| C | limpa o rastro |
| F | tela cheia |
| P | salva imagem |
| T | alterna tema |
| ? | abre a ajuda |

## Tecnologias

Tudo client-side, sem backend e sem etapa de build:

- HTML/CSS/JS puro para a interface e a física
- Three.js (r128) + OrbitControls para a cena 3D em WebGL
- Bootstrap Icons pros ícones

As libs vêm de CDN direto no `index.html`, então precisa de internet mesmo rodando local.

## Estrutura

```
index.html
src/
  css/style.css
  js/app.js
  images/magnet.svg
```

## Rodando localmente

```bash
git clone https://github.com/pedrokaliel/simulador-forca-lorentz.git
cd simulador-forca-lorentz
```

Só abrir o `index.html` no navegador, sem precisar de servidor nem de instalar nada.

## Deploy

Publicado na Vercel a partir da branch `main`: https://simulador-forca-lorentz.vercel.app

## Equipe

Pedro Kaliel Vieira Lima, Gabriel Leite Pasqualli, Thalys Soares de Lima, Jose Manoel Lobo Sales e Luiz Henrique da Silva Bezerra.

## Licença

Projeto acadêmico, sem licença definida por enquanto.
