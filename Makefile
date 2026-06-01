# Packaging for ICFP Artifact Evaluation.
#
#   make package   # build a clean zip containing only source + build files
#   make test      # run the full test suite
#   make clean     # remove build output and the packaged zip

ARTIFACT := let-it-be-optimized-artifact
DIST     := dist
STAGE    := $(DIST)/$(ARTIFACT)
ZIP      := $(DIST)/$(ARTIFACT).zip

# Only code and the files needed to build/run it are shipped.
FILES    := build.sbt README.md
PROJECT  := project/build.properties project/plugins.sbt

.PHONY: package
package:
	rm -rf $(STAGE) $(ZIP)
	mkdir -p $(STAGE)/project
	cp $(FILES) $(STAGE)/
	cp $(PROJECT) $(STAGE)/project/
	cp -r src $(STAGE)/src
	# Drop anything that is not source: build output and OS/editor cruft.
	find $(STAGE) -type d -name target -prune -exec rm -rf {} +
	find $(STAGE) -type f -name '.DS_Store' -delete
	find $(STAGE) -type f -name 'README.md' -delete
	cd $(DIST) && zip -r $(ARTIFACT).zip $(ARTIFACT) >/dev/null
	@echo "Created $(ZIP):"
	@unzip -l $(ZIP)

.PHONY: test
test:
	sbt test

.PHONY: clean
clean:
	sbt clean
	rm -rf $(DIST)
