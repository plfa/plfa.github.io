require 'fileutils'

guard :shell do
  watch(%r{^(.+)\.lagda\.md$}) do |m|
    src = m[0]
    out = "#{File.dirname(src).sub('src','out')}/#{File.basename(src,'.lagda.md')}.md"
    `make #{out}` unless File.basename(src).start_with?('.#')
  end
end
