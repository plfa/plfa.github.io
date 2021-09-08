SITE_DIR := _site

.PHONY: build
build:
	@stack build --silent && stack run

.PHONY: serve
serve:
	@echo "Starting server..."
	@cd $(SITE_DIR) && \
		browser-sync start \
			--server \
			--files "." \
			--no-ui \
			--reload-delay 500 \
			--reload-debounce 500

.PHONY: clean
clean:
	@rm -rf _build

.PHONY: clobber
clobber: clean
	@rm -rf _site
