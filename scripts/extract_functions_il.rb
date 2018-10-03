#!/usr/bin env ruby

$:.unshift File.dirname(__FILE__)

require 'bap'

bap_home = ENV['BAP_HOME']

if bap_home.nil?
	puts "BAP_HOME not defined!"
	exit 1
end

bap = Bap.new bap_home

binary = ARGV.shift

bap.function_boundaries(binary).each do |f|
	puts "[+] Extracting #{f[:function]}"
	cmd = "#{File.join(bap_home,'utils', 'iltrans')} -pp-ast #{File.basename(binary)}_#{f[:function]}.il -binrange #{binary} #{f[:start]} #{f[:stop]} 2> /dev/null"
	unless system(cmd) 
		puts "Unable to lift il for function #{f[:function]} using #{cmd}"
	end
end
