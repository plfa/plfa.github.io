require 'fileutils'

guard :shell do
  watch(%r{^.+\.(lagda)$}) do |m|
    src = m[0]
    out = "#{File.dirname(src).sub('src','out')}/#{File.basename(src,'.*')}.md"
    `make #{out}` unless File.basename(src).start_with?('.#')
  end
end
