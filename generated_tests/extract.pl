#!/usr/bin/perl -w

open(logfile, "$ARGV[$0]")
    or die ("Cannot open log file");

my $flag = 0;
while(<logfile>) {
    if($flag == 1) {
	if(/\S/) {
	    print;
	}
	else {
	    print "segfault or timeout\n";
	}
	$flag = 0;
    } 
    if(/\*\*\*/) {
	$flag = 1; 
    }
}
