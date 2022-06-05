#!/usr/bin/env ruby
require 'yaml'
require 'liquid'

unless ARGV.length == 3
  abort "Usage: render-liquid-template.rb [yaml_file] [markdown_in_file] [markdown_out_file]"
end

yaml_file, markdown_file_in, markdown_file_out = ARGV

[yaml_file, markdown_file_in].each do |file|
  unless File.file? file
    abort "File does not exist: '%s'" % [file]
  end
end

metadata = { 'site' => (YAML.load (File.read yaml_file)) }
template = Liquid::Template.parse (File.read markdown_file_in)
File.write markdown_file_out, (template.render metadata)
