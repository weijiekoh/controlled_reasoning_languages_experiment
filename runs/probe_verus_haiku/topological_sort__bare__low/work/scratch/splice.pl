use strict;
my ($orig) = @ARGV;
local $/; open my $f, '<', $orig or die; my $s = <$f>; close $f;
my %body = (
  "helpers" => do { local $/; open my $h, '<', '/work/scratch/helpers.rs'; <$h> },
  "proofs"  => "",
  "code"    => do { local $/; open my $c, '<', '/work/scratch/code.rs'; <$c> },
);
for my $tag (qw(helpers proofs code)) {
  my $start = "// <$tag>"; my $end = "// </$tag>";
  my $i = index($s, $start); my $j = index($s, $end);
  die "markers $tag" if $i < 0 || $j < 0 || index($s,$start,$i+1) >= 0;
  $s = substr($s, 0, $i + length($start)) . "\n" . $body{$tag} . substr($s, $j);
}
print $s;
