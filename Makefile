.PHONY: build
build:
	stack build && stack exec site build

.PHONY: watch
watch:
	stack build && stack exec site watch

.PHONY: clean
clean:
	stack build && stack exec site clean

.PHONY: update-contributors
update-contributors:
	stack build && stack exec update-contributors
