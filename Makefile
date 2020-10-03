#################################################################################
# Build PLFA site
#################################################################################

.PHONY: build
build:
	stack build && stack exec site build

#################################################################################
# Automatically rebuild the site on changes, and start a preview server
#################################################################################

.PHONY: watch
watch:
	stack build && stack exec site watch


#################################################################################
# Clean up and remove the cache
#################################################################################

.PHONY: clean
clean:
	stack build && stack exec site clean


#################################################################################
# Update contributor metadata in `contributors/`
#################################################################################

.PHONY: update-contributors
update-contributors:
	stack build && stack exec update-contributors


#################################################################################
# List targets in Makefile
#################################################################################

.PHONY: list
list:
	@$(MAKE) -pRrq -f $(lastword $(MAKEFILE_LIST)) : 2>/dev/null | awk -v RS= -F: '/^# File/,/^# Finished Make data base/ {if ($$1 !~ "^[#.]") {print $$1}}' | sort | egrep -v -e '^[^[:alnum:]]' -e '^$@$$'
