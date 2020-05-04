zip:
	rm -rf hb-final
	mkdir -p hb-final
	cp \
		biblio.bib \
		cc-by.pdf \
		elpi.py \
		hb.tex \
		lipics-logo-bw.pdf \
		lipics-v2019.cls \
		orcid.pdf \
		puzzle.pdf \
		v4.pdf \
		hb-final
	zip -r hb.zip hb-final
