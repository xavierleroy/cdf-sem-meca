# Sémantiques mécanisées: le développement Coq

Ce dépôt contient les sources Coq pour le cours 
["Sémantiques mécanisées"](https://www.college-de-france.fr/site/xavier-leroy/course-2019-2020.htm)
de Xavier Leroy au Collège de France en 2019-2020.

Cette version est commentée en français.  The English version is available [here](https://github.com/xavierleroy/cdf-mech-sem).

Un rendu HTML des sources commentés est également disponible:

1. La sémantique d'un langage impératif
   * Module [IMP](https://xavierleroy.org/cdf-sem-meca/CDF.IMP.html): le langage impératif IMP et ses sémantiques.
   * Bibliothèque [Sequences](https://xavierleroy.org/cdf-sem-meca/CDF.Sequences.html): définitions et propriétés des suites de réductions.

2. Vérification formelle d'un compilateur
   * Module [Compil](https://xavierleroy.org/cdf-sem-meca/CDF.Compil.html): compilation de IMP vers une machine virtuelle.
   * Bibliothèque [Simulation](https://xavierleroy.org/cdf-sem-meca/CDF.Simulation.html): diagrammes de simulation entre deux systèmes de transitions.

3. Optimisations, analyses statiques, et leur vérification
   * Module [Optim](https://xavierleroy.org/cdf-sem-meca/CDF.Optim.html): optimisations à base d'analyse de vivacité.
   * Bibliothèque [Fixpoints](https://xavierleroy.org/cdf-sem-meca/CDF.Fixpoints.html): calcul de points fixes par itération de Knaster-Tarski.

4. Des logiques pour raisonner sur les programmes
   * Module [HoareLogic](https://xavierleroy.org/cdf-sem-meca/CDF.HoareLogic.html): des logiques de Hoare faible et forte pour IMP.
   * Module [SepLogic](https://xavierleroy.org/cdf-sem-meca/CDF.SepLogic.html): une logique de séparation pour IMP plus pointeurs et allocation dynamique.

5. L'analyse statique par interprétation abstraite
   * Module [AbstrInterp](https://xavierleroy.org/cdf-sem-meca/CDF.AbstrInterp.html): un analyseur statique par interprétation abstraite.
   * Module [AbstrInterp2](https://xavierleroy.org/cdf-sem-meca/CDF.AbstrInterp2.html): une amélioration de l'analyseur statique précédent.

6. Sémantiques de la divergence
   * Module [Divergence](https://xavierleroy.org/cdf-sem-meca/CDF.Divergence.html): sémantique dénotationnelle classique, sémantique naturelle coinductive.
   * Module [Partiality](https://xavierleroy.org/cdf-sem-meca/CDF.Partiality.html): monade de partialité et sémantique dénotationnelle constructive.

7. Sémantique et typage d'un langage fonctionnel
   * Module [FUN](https://xavierleroy.org/cdf-sem-meca/CDF.FUN.html): le langage fonctionnel FUN et son système de types.
