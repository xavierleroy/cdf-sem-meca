include CoqMakefile

CoqMakefile:
	coq_makefile -f _CoqProject -o CoqMakefile

documentation:
	coq2html -base CDF -short-names -d docs *.glob *.v
