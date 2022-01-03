# Hitachi Hokudai Lab. & Hokkaido University Contest 2021 Tool

本ツールは、[Hitachi Hokudai Lab. & Hokkaido University Contest 2021](https://atcoder.jp/contests/hokudai-hitachi2021)向けの非公式ツールです。動作保証はありませんので、自己責任でご利用ください。

本ソフトウェアはMIT Licenseの下で公開されています。

## 提供物

### A問題向け

- ビジュアライザ(vis_a.html)
  - マップの情報(位置関係、人口、面積、土地価格、距離)が表示可能です
  - EV・orderの動きやスコア情報が表示可能です
  - 使用方法
    - Inputファイルを読み込むことでマップ情報が表示されます
    - EV・orderの動きやスコアを表示する場合は、a/judge_A.cppをコンパイルしたジャッジツールを使用してvislogファイルを出力し、ビジュアライザに読み込ませてください
  - 災害対応モードには対応していません

### B問題向け

- ビジュアライザ(vis_b.html)
  - マップの情報(位置関係、人口、面積、土地価格、距離)が表示可能です
  - EV・orderの動きやスコア情報が表示可能です
  - 使用方法
    - Inputファイルを読み込むことでマップ情報が表示されます
    - EV・orderの動きやスコアを表示する場合は、b/judge_B.cppをコンパイルしたジャッジツールを使用してvislogファイルを出力し、ビジュアライザに読み込ませてください
  - 作業の内容表示には対応していません
  - 災害対応モードには対応していません

## 変更履歴

- 2021.12.13 初版
- 2021.12.19 EV,orderの動作表示対応
- 2022.01.03 B問題ビジュアライザ追加
