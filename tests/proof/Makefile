# Settings
# --------

specs_dir:=specs
build_dir:=.build

.PHONY: all clean

all: split-proof-tests

clean:
	rm -rf $(specs_dir)

# Spec Files
# ----------

erc20_files:=totalSupply-spec.k \
             balanceOf-spec.k \
             allowance-spec.k \
             approve-success-spec.k \
             approve-fail-spec.k \
             transfer-success-1-spec.k \
             transfer-success-2-spec.k \
             transfer-failure-1-spec.k \
             transfer-failure-2-spec.k \
             transfer-failure-3-spec.k \
             transferFrom-success-1-spec.k \
             transferFrom-success-2-spec.k \
             transferFrom-failure-1-spec.k \
             transferFrom-failure-2-spec.k

proof_tests:=erc20

split-proof-tests: $(proof_tests)

erc20: $(patsubst %, $(specs_dir)/erc20/%, $(erc20_files))

# ERC20
erc20_tmpls:=erc20/module-tmpl.k erc20/spec-tmpl.k

$(specs_dir)/erc20/%-spec.k: $(erc20_tmpls) erc20/erc20-spec.ini
	@echo >&2 "==  gen-spec: $@"
	mkdir -p $(dir $@)
	python3 resources/gen-spec.py $^ $* $* > $@
	cp erc20/verification.k $(dir $@)
