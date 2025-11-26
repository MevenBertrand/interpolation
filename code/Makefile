# Inspired from https://github.com/palmskog/coq-program-verification-template

all: interpolation

autosubst:
	autosubst -f -s urocq -v ge813 -p ./theories/Ast_preamble -no-static -o ./theories/Ast.v ./theories/Ast.sig

interpolation: Makefile.rocq
	@+$(MAKE) -f Makefile.rocq all

clean: Makefile.rocq
	@+$(MAKE) -f Makefile.rocq cleanall
	@rm -f Makefile.rocq Makefile.rocq.conf

Makefile.rocq: _CoqProject
	$(ROCQBIN)rocq makefile -f _CoqProject -o Makefile.rocq

force _CoqProject Makefile: ;

%: Makefile.rocq force
	@+$(MAKE) -f Makefile.rocq $@

.PHONY: all clean force interpolation autosubst