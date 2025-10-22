all: build test doc package_upload doc_upload
all_butno_package: build test doc 
	
build:
	@echo "_______________Build___________"
	@rm -rf ./build/*
	@rm -rf *.tix
	@rm -rf hpc*.html
	cabal clean
	cabal update
	cabal build

test:
	@echo "_______________Testing__________"
	cabal test 

doc:
	@echo "creating documentation"
	--cabal v2-haddock --haddock-for-hackage --haddock-hyperlink-source --haddock-quickjump --enable-doc
	--cabal haddock --haddock-executables --haddock-for-hackage --haddock-hyperlink-source --haddock-quickjump --enable-doc  
	cabal haddock --haddock-for-hackage --haddock-hyperlink-source --haddock-quickjump --enable-doc  

benchmark:
	@echo "creating benchmarks"
# 	cabal bench --benchmark-options='--timeout 10000000' --benchmark-options='+RTS -I0 -A16m -N3 -H24m'
	cabal bench integer-roots-benchmark --benchmark-options "+RTS -I0 -K256m -A16m -N8 -H24m -T -w -RTS --output=integer-roots.html"
	hpc report integer-roots-benchmark 
	hpc markup integer-roots-benchmark

bench_weigh:
	@echo "creating benchmarks weigh"
	cabal bench weigh

profile:
	@echo "_____________________creating profile___________"
	cabal clean
# 	cabal configure --enable-library-profiling --enable-executable-profiling
	cabal build --enable-library-profiling  --enable-executable-profiling
	@rm -rf *.tix
	cabal run integer-roots-exe -- +RTS -p -s -N4

profile_stack:
	@echo "creating profile w/stack"
	stack build --profile
	stack exec -- grfn-exe  100000 +RTS -p -N4 -RTS

main:
	@echo "creating main"
	@rm -rf *.tix
# 	cabal run integer-roots-exe -- +RTS -N4
	cabal run integer-roots-exe "+RTS -I0 -K256m -A16m -N8 -H24m -T -w -RTS --output=integer-roots.html" -p

package_upload:
	@echo "creating tarball"
	rm -rf ./dist-newstyle/sdist/*.tar.gz
	cabal sdist
	cabal upload --publish dist-newstyle/sdist/*.tar.gz

doc_upload:
	@echo "uploading docs hack"
	rm -rf ./dist-docs/*
	cabal haddock --builddir=dist-docs --haddock-for-hackage --haddock-option=--hyperlinked-source
	cabal upload --publish -d dist-docs/*-docs.tar.gz