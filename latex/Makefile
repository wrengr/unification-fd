FILES=\
	unification-intro-mcmaster \
	unification-opt-mcmaster

EXTRA_FILES={dvi,ps,ptb}

.SUFFIXES:
.PHONY: all clean realclean

all:
	@# TODO: update latexmk to call lhs2TeX?
	for f in ${FILES} ; do                           \
		if [ -e "$$f.lhs" ] ; then                   \
			lhs2TeX "$$f".lhs -o "$$f".tex || break ;\
		fi                                          ;\
		latexmk -pdfps "$$f".tex           || break ;\
	done

clean:
	for f in ${FILES} ; do             \
		latexmk -c "$$f".tex || break ;\
	done

realclean:
	@# TODO: also remove BibTeX logs, makeindex logs,...
	@# TODO: update latexmk to remove all these...
	for f in ${FILES} ; do                   \
		if [ -e "$$f".tex ] ; then           \
			latexmk -C "$$f".tex   || break ;\
		fi                                  ;\
		rm -f "$$f".${EXTRA_FILES} || break ;\
		if [ -e "$$f".lhs ] ; then           \
			rm -f "$$f".tex        || break ;\
		fi                                  ;\
	done
