# find_and_move.ps1
# Run from VSCode terminal - finds Backup folder automatically
# Usage: just run from anywhere in the project

# First find where Backup folder is
$searchRoot = "C:\Users\tarth\Membership_Project"
$backupFolder = Get-ChildItem -Path $searchRoot -Recurse -Directory -Filter "Backup" |
                Select-Object -First 1 -ExpandProperty FullName

if (-not $backupFolder) {
    Write-Host "Backup folder not found under $searchRoot"
    Write-Host "Creating it at: $searchRoot\MembershipProject\Backup"
    $backupFolder = "$searchRoot\MembershipProject\Backup"
    New-Item -ItemType Directory -Path $backupFolder
}

Write-Host "Backup folder found at: $backupFolder"

# Core folder
$coreFolder = "$searchRoot\MembershipProject\Core"
Write-Host "Core folder: $coreFolder"
Write-Host ""

$files = @(
    "N_Necessity.lean",
    "N_Adjacency_.lean",
    "N_Adjacency_R.lean",
    "N_Cardinality.lean",
    "N_Check2Pedigree.lean",
    "N_CheckToPedigree.lean",
    "N_Claim2Pedigrees.lean",
    "N_DesirableDef.lean",
    "N_Desired2Ped.lean",
    "N_DesiredToPed.lean",
    "N_Equivalence.lean",
    "N_EquivalencePedDesired.lean",
    "N_HC2Pedigree.lean",
    "N_HC2Pedigree_hpair.lean",
    "N_HCNaturalInKn.lean",
    "N_HCToPedigree.lean",
    "N_MIRLemma.lean",
    "N_Ped2Desired.lean",
    "N_PedigreeAdjacency.lean",
    "N_PedigreeEquiv.lean",
    "N_PedigreeGraph.lean",
    "N_PedigreeStep.lean",
    "N_RationalityGuarantee.lean",
    "N_RestrictionAll.lean",
    "N_RigidAdj_Case2a.lean",
    "N_RigidAdj_Case2b.lean",
    "N_RigidAdj_Case2c.lean",
    "N_Rigidity.lean",
    "N_EdgeInKTour.lean",
    "EdgeInKTour.lean",
    "HCNatualInKn.lean",
    "LearningFinsetDesirableDef.lean",
    "PartitionProbabilityFlowProblem.lean",
    "ProbabilityPartitionAndPedigreeApplicationVer1.lean",
    "k_tour_final.lean"
)

$moved = 0
$skipped = 0

foreach ($f in $files) {
    $src = Join-Path $coreFolder $f
    if (Test-Path $src) {
        Move-Item $src $backupFolder
        Write-Host "Moved: $f"
        $moved++
    } else {
        Write-Host "Not found: $f"
        $skipped++
    }
}

Write-Host ""
Write-Host "Done. Moved=$moved  Skipped=$skipped"
Write-Host ""
Write-Host "Verify with:"
Write-Host "  cd $searchRoot"
Write-Host "  lake build MembershipProject.Core.N_PEqualsNP"