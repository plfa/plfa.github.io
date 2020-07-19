source "https://rubygems.org"

group :jekyll_plugins do
  gem 'github-pages'
end

group :development do
  gem 'guard'
  gem 'guard-shell'
  gem 'html-proofer'
  # ffi-1.13.1 is broken on macos
  # https://github.com/ffi/ffi/issues/791
  gem 'ffi', '~> 1.12.2'
end

group :epub do
  gem 'safe_yaml'
  gem 'liquid'
end
