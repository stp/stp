#!/usr/bin/perl -w

# Run STP regression tests of a given level (default: 0, meaning
# minimum amount of tests).  The higher the regression level, the more
# tests to run, and the harder they get.
# Each test may contain information about its regression level,
# expected outcome, expected runtime, whether it produces a proof,
# etc. in the format given below.  This script will scan the first 100
# lines of each test and try to collect this information.

# If some info is not found, defaults are assumed.  Default regression
# level is 0, expected runtime is unbounded, outcome is undefined
# (whatever it returns is OK), proof should be produced if outcome is
# Valid, and if it is produced, it'll be verified.

# Test info is given in the comments; here are examples
# 
# %%% Regression level = 2
# %%% Result = Valid  %% or Invalid, or Unknown
# %%% Runtime = 10   %% in seconds
# %%% Proof = yes    %% or 'no', if it doesn't produce a proof
# %%% Language = presentation %% or 'internal'

# The number of '%' and following spaces can vary, case is not
# important.  Any text after the value is ignored.  Any comments that
# are not recognized are also ignored.

use strict;

my %optionsHelp =
    ("-h" => "Print this help and exit",
     "-v" => "Be verbose (default, opposite of -q)",
     "-q" => "Quiet mode (opposite of -v)",
     "-l n" => "Set regression level (default 0, the easiest level)",
     "+rt" => "Check that each test finishes within the specified runtime",
     "-rt" => "Do not check whether test finishes within the specified runtime (default)",
#      "+proofs" => "Produce and verify proofs",
#      "-proofs" => "Do not produce / verify proofs (default)",
     "-lang name" => "Use the named input language only (default=all)",
     "-t secs" => "Run each executable for at most 'secs' seconds [0 = no limit]",
     "-vc prog" => "Use \"prog\" to run STP (default=bin/stp)",
     "-pfc prog" => "Use \"prog\" to run a proof checker (default=true)"
     );

my $usageString =
    "run_tests [ options ] [ test1 test2 ... ] [ -- [ stp options ] ]

Run STP Lite regression tests.  Concrete test files or directories
with test files should be specified by name with a full path or
relative path to the current directory.  If none specified, all
subdirectories are searched for test files.

Default running mode is overriden by test specs;
test specs are overriden by command line options.

Options:
  " . join("\n  ",
	   map { sprintf("%-9s %s", $_, $optionsHelp{$_}) } keys(%optionsHelp));

my $pwd = `pwd` ;
chomp $pwd ;

# Database of default values for options
my %optionsDefault = ("level" => 4,
		      "verbose" => 1,
                      "rt" => 1,
		      "proofs" => 0,
		      "lang" => "all",
		      "stppath" => "stp/bin",
		      "vc" => $pwd . "/bin/stp -d", # Program names
		      #"vc" => "valgrind --leak-check=full /home/vganesh/stp/bin/stp", # Program names
		      "pfc" => "true",
		      "stptestpath" => "stp/test",
		      "stptemp" => "/tmp",
		      # max. number of lines to read from the testcase file
		      # when looking for info comments
		      "maxInfoLines" => 4,
		      # Runtime limit; 0 = no limit
		      "time" => 180,
		      # Additional command line options to stp
		      "stpOptions" => "-d");

# Database of command line options.  Initially, they are undefined
my %options = ();
# The list of testcases to run
#
#my @testcases = "sample-tests";
my @testcases = "../../stp-tests/synthesis-tests/";
# Temporary array for STP options
my @stpOptions = ();
# State is either "own" or "stp", meaning that we're reading either
# our own or stp's options.
my $argState = "own";

if($#stpOptions >= 0) {
    $options{'stpOptions'} = join(" ", map { "\"" . $_ . "\"" } @stpOptions);
}

# Compute the value of the option: first check the command line
# option, then the supplied database (by ref. as the second arg), then
# default values database.  If it cannot find definition, it is a bug,
# and the script is stopped.

sub getOpt {
    my ($name, $dbRef) = @_;
    
    return $options{$name} if(defined($options{$name}));
    return $dbRef->{$name} if(defined($dbRef) && defined($dbRef->{$name}));
    return $optionsDefault{$name} if(defined($optionsDefault{$name}));
    
    # Option value is not found
    die "getOpt($name): option is undefined";
}

my $verbose = getOpt('verbose');

# Set the path
my $systemPath = ".";
if(defined($ENV{'PATH'})) {
    $systemPath = $ENV{'PATH'};
}
$ENV{'PATH'} = getOpt('stppath') . ":" . $systemPath;

if($verbose) {
    print "*********\n";
    print("Regression level: ", getOpt('level'), "\n");
    print("Language: ", getOpt('lang'), "\n");
    print("Whether to produce / check proofs: ",
	  (defined($options{'proofs'}))?
	  (($options{'proofs'})? "yes" : "no") : "depends on testcase",
	  "\n");
    if(getOpt('time') > 0) {
	print("Time limit per test: ", getOpt('time'), " sec\n");
    }
    print("PATH = ", $ENV{'PATH'}, "\n");
    print "*********\n";
}

my $tmpdir = getOpt('stptemp') . "/stptmp-$$";
my $currdir = `pwd`;
my $stp = getOpt('vc');
my $pfc = getOpt('pfc');
my $level = getOpt('level');
my $lang = getOpt('lang');
my $rt = getOpt('rt');

# Read the first 'maxInfoLines' of the testcase and fetch information
# from the comments

sub getTestOpt {
    my ($name) = @_;
    # This is what we return
    my %db = ();

    open IN, $name or die "Cannot open $name: $?";
    for(my $lines = getOpt('maxInfoLines'), my $str = <IN>;
	defined($str) && $lines > 0;
	$lines--, $str = <IN>)
    {
	if($str =~ /^(\s|%|\#)*Regression level\s*=\s*(\d+)/i) {
	    $db{'level'} = $2;
	}
	if($str =~ /^(\s|%|\#)*Result\s*=\s*(Valid|Invalid|Unknown)/i) {
	    $db{'result'} = lc $2;
	}
	if($str =~ /^(\s|%|\#)*Runtime\s*=\s*(\d+)/i) {
	    $db{'runtime'} = $2;
	}
	if($str =~ /^(\s|%|\#)*Proof\s*=\s*(yes|no)/i) {
	    if($2 eq "yes") { $db{'proofs'} = 1; }
	    else { $db{'proofs'} = 0; }
	}
	if($str =~ /^(\s|%|\#)*SAT mode\s*=\s*(on|off)/i) {
	    if($2 eq "on") { $db{'sat'} = 1; }
	    else { $db{'sat'} = 0; }
	}
	if($str =~ /^(\s|%|\#)*Language\s*=\s*((\w|\d|\_)+)/i) {
	    $db{'lang'} = lc $2;
	}
	if($str =~ /^(\s|%|\#)*STP Options\s*=\s*(.*)$/i) {
	    $db{'stpOptions'} = $2;
	}
    }
    close IN;

    # If regression level is not set, make it 3. So, if a lower level
    # is requested, only explicitly marked tests will be run.
    if(!defined($db{'level'})) { $db{'level'}=3; }
    # If the input language is not defined, guess it by extension
    if(!defined($db{'lang'})) {
	if($name =~ /\.(stp|svc)$/) {
	    $db{'lang'} = "presentation";
	} elsif($name =~ /\.(li?sp)$/) {
	    $db{'lang'} = "internal";
	} elsif($name =~ /\.(smt)$/) {
	    $db{'lang'} = "smt-lib";
	}
    }

    return %db;
}

# Total number of tests run
my $testsTotal=0;
# Total number of proofs checked by pfc
my $proofsChecked=0;
# Total number of tests with problems (each test is counted at most once)
my $testsProblems=0;
### Database of results
# It is a hash mapping problem keys to arrays of testcase names.
# Only problematic testcase are inserted here.
# Keys are: fail, result, proof, noproof (no proof generated when should),
# time, timeTooMuch, lang (wrong language),
# error (stp reported errors, but didn't die)
my %testsDB=();

# Search for a string element in the array ref, and return 1 if found, 0 if not
sub findStringElement {
    my ($el, $aRef) = @_;
    foreach my $v (@{$aRef}) {
	if($v eq $el) { return 1; }
    }
    return 0;
}

# Add a testcase to the set of problematic runs.
# Args: 
#   test is the full or relative path to the test file
#   lang is the input language (not used currently)
#   problem is the name of the problem the testcase exhibits
sub addProblem {
    my ($test, $lang, $problem) = @_;
    my $aRef = $testsDB{$problem};
    if(!defined($aRef)) { $aRef=[ ]; }
    if(!findStringElement($test, $aRef)) {
	$testsDB{$problem} = [@{$aRef}, $test];
    }
}

# Total running time
my $totalTime = time;
my $defaultDir = `pwd`;
$defaultDir =~ s/\n//;

foreach my $testcase (@testcases) {
    chdir $defaultDir or die "Cannot chdir to $defaultDir: $?";
    my @testcasesTmp = ();
    if(-f $testcase) { push @testcasesTmp, $testcase; }
    elsif(-d $testcase) {
	# Compute the list of files for testcases
	opendir(TESTS, $testcase)
	    or die "Cannot open directory $testcase: $?";
	@testcasesTmp = grep {
	    /[.]([sc]vcl?|li?sp|smt|stp)$/ && -f "$testcase/$_" } readdir(TESTS);
	closedir TESTS;
	@testcasesTmp = map { "$testcase/$_" } @testcasesTmp;
    } else {
	print("*** Error: WARNING: cannot find testcase $testcase: ",
	      "no such file or directory\n");
    }

    for(my $i=0; $i<=$#testcasesTmp; $i++) {
	my $name = $testcasesTmp[$i];
	my $file = "$defaultDir/$name";
	my $hasProblem=0;
	if(!(-f $file)) {
	    print "Error: WARNING: no such file: $file\n";
	    next;
	}
	my %opt = getTestOpt($file);
	# Check regression level
	if(defined($opt{'level'}) && $level < $opt{'level'}) {
	    # Regression level of this test is too high; skip it
	    next;
	}
	# Print the testcase name
	print("===============================================\n",
	      $testcasesTmp[$i], ":\n");
	# Check the input language
	if($lang ne "all" && defined($opt{'lang'}) && $lang ne $opt{'lang'}) {
	    print "Error: Wrong input language, skipping $testcasesTmp[$i]\n";
	    $hasProblem=1;
	    addProblem($name, $lang, 'lang');
	    next;
	}
	my $checkProofs = getOpt('proofs', \%opt);
	my $expRuntime = $opt{'runtime'};
	my $expResult = $opt{'result'};
	my $stpOptions = getOpt('stpOptions', \%opt);
	# Print some testcase specific info
	if($verbose) {
	    print("Language: $lang\n");
	    print("Checking proofs: ", ($checkProofs)? "yes" : "no",
		  "\n");
	    #if($rt && defined($expRuntime)) {
	    if(defined($expRuntime)) {
		print("Expected runtime: ", $expRuntime, " sec\n");
	    }
	    if(defined($expResult)) {
		print("Expected result: ", $expResult, "\n");
	    }
	    if($stpOptions =~ /\S/) {
		print("STP options: ", $stpOptions, "\n");
	    }
	}
	# Create a temporary dir, but first delete it; there may be
	# junk there
	system("/bin/rm -rf $tmpdir");
	mkdir $tmpdir or die "Cannot create directory $tmpdir: $?";
	chdir $tmpdir or die "Cannot chdir to $tmpdir: $?";

	# Compute stp arguments
	my @stpArgs = ();
	# push @stpArgs, ($checkProofs)? "+proofs" : "-proofs";
	# if($lang ne "all") { push @stpArgs, "-lang $lang"; }
	# push @stpArgs, $stpOptions;
	# my $stpArgs = join(" ",  @stpArgs);
	# Now, run the sucker
	my $timeMax = getOpt('time');
	my $timeLimit = ($timeMax > 0)? "-t $timeMax" : "";
	my $limits = "ulimit -c 0; ulimit -d 2000000; ulimit -m 2000000; ulimit -v 2000000; ulimit $timeLimit";
	#   "-s 10240 -v 2000000 $timeLimit";	
	my $logging = ($verbose)? " 2>&1 | tee output" : "> output 2>&1";
	my $timing = ($verbose)? "time " : "";
	if($verbose) {
	    print "***\n";
	    #print "Running $stp $stpArgs < $file\n";
	    print "Running $stp < $file\n";
	    print "***\n";
	}
	my $time = time;
	# my $exitVal = system("$limits; $timing $stp $stpArgs "
	my $exitVal = system("$limits; $timing $stp "
	#my $exitVal = system("$timing $stp "
			     . "< $file $logging");
	$time = time - $time;
	# OK, let's see what happened
	$testsTotal++;
	# Printing runtime
	print "Runtime: $time sec";
	if($rt && defined($expRuntime)) {
	    if($time > $expRuntime) {
		if($time > 10*$expRuntime) {
		    print " MUCH";
		    addProblem($name, $lang, 'timeTooMuch');
		}
		print " : LONGER than expected: $expRuntime sec";
		$hasProblem=1;
		addProblem($name, $lang, 'time');
	    }
	    elsif($expRuntime >= 5 && $time < $expRuntime/2) {
                print " : much FASTER than expected: $expRuntime sec";
                addProblem($name, $lang, 'timeFast');
                $hasProblem=1;
            }
	}
	print "\n";
	# Parsing the output
	open IN, "output" or die "Cannot open `pwd`/output: $?";
	my $str;
	my $result="";
	my $hasErrors=0;
	while(defined($str=<IN>)) {
	    # Find at least one valid result
	    if($result ne "valid" && $str =~ /^(Valid|In[Vv]alid|Unknown)./) {
		$result=lc $1;
	    }
	    # STP exit value may be masked by the shell pipe.  Fish it
	    # out from the output
	    if($str =~ /^(Interrupted|Segmentation|Bus error|Floating point exception|.*exception)/) {
		$exitVal = $1;
	    }
	    if($str =~ /^(\*|\s)*((parse\s+)?[Ee]rror)/) {
		$hasErrors=1;
	    }
	}
	close IN;
	if($exitVal ne "0") {
	    print "*** Error: STP FAILED with exit code $exitVal\n";
	    $hasProblem=1;
	    addProblem($name, $lang, 'fail');
	}
	# Checking for errors
	if($hasErrors) {
	    $hasProblem=1;
	    addProblem($name, $lang, 'error');
	    print "ERRORS in the test\n";
	}
	# Printing result diagnostics
	if(defined($expResult)) {
	    if($expResult ne $result) {
		$hasProblem=1;
		if($result eq "") {
		    addProblem($name, $lang, 'fail');
		    print("Error: FAILED (no result, expected $expResult)\n");
		} else {
		    addProblem($name, $lang, 'result');
		    print("Error: WRONG RESULT (", $result,
			  " instead of $expResult)\n");
		}
	    } else {
		print "Result is correct\n";
	    }
	}
	# else {
# 	    print "Error: No result\n";
# 	}
	$testsProblems += $hasProblem;
	print("=============== End of testcase ===============\n");
    }
}

$totalTime = time - $totalTime;

print "\nStatistics:\n";
print "Total tests run: $testsTotal\n";
print "Total running time: $totalTime sec\n";
print "Total number of proofs checked: $proofsChecked\n";
print "Problematic cases: $testsProblems\n";
if($testsProblems > 0 && $verbose) {
    my $aref;
    print "\nDetailed Statistics:\n";
    $aref=$testsDB{'fail'};
    if(defined($aref)) {
	my @a = @{$aref};
	printf("Failed tests [%d]:\n", $#a+1);
	foreach my $n (@a) { print "  $n\n"; }
    }
    $aref=$testsDB{'error'};
    if(defined($aref)) {
	my @a = @{$aref};
	printf("Tests with errors [%d]:\n", $#a+1);
	foreach my $n (@a) { print "  $n\n"; }
    }
    $aref=$testsDB{'result'};
    if(defined($aref)) {
	my @a = @{$aref};
	printf("Tests with wrong results [%d]:\n", $#a+1);
	foreach my $n (@a) { print "  $n\n"; }
    }
    $aref=$testsDB{'proof'};
    if(defined($aref)) {
	my @a = @{$aref};
	printf("Tests with failed proofs [%d]:\n", $#a+1);
	foreach my $n (@a) { print "  $n\n"; }
    }
    $aref=$testsDB{'noproof'};
    if(defined($aref)) {
	my @a = @{$aref};
	printf("Tests that should have proofs but don't [%d]:\n", $#a+1);
	foreach my $n (@a) { print "  $n\n"; }
    }
    $aref=$testsDB{'timeFast'};
    if(defined($aref)) {
	my @a = @{$aref};
	printf("Tests running at least twice as fast as expected [%d]:\n", $#a+1);
	foreach my $n (@a) { print "  $n\n"; }
    }
    $aref=$testsDB{'time'};
    if(defined($aref)) {
	my @a = @{$aref};
	printf("Tests running longer [%d]:\n", $#a+1);
	foreach my $n (@a) { print "  $n\n"; }
    }
    $aref=$testsDB{'timeTooMuch'};
    if(defined($aref)) {
	my @a = @{$aref};
	printf("...including tests running WAY too long [%d]:\n", $#a+1);
	foreach my $n (@a) { print "  $n\n"; }
    }
    $aref=$testsDB{'lang'};
    if(defined($aref)) {
	my @a = @{$aref};
	printf("Tests with wrong input language [%d]:\n", $#a+1);
	foreach my $n (@a) { print "  $n\n"; }
    }
}

# Delete temporary dir if there is one
system("/bin/rm -rf $tmpdir");

#exit ($testsProblems > 0 ? 2 : 0);

