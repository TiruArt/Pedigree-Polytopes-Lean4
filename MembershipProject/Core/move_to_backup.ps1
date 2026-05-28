# move_to_backup.ps1
# Run from: C:\Users\tarth\Membership_Project
# Usage: .\move_to_backup.ps1

$core = "MembershipProject\Core"
$aux  = "MembershipProject\Backup"

# Create Backup folder
New-Item -ItemType Directory -Force -Path $aux

$files = @(
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

foreach ($f in $files) {
    $src = Join-Path $core $f
    if (Test-Path $src) {
        Move-Item $src $aux
        Write-Host "Moved: $f"
    } else {
        Write-Host "Not found (skipped): $f"
    }
}

Write-Host ""
Write-Host "Done. Now run: lake build MembershipProject.Core.N_PEqualsNP"
Write-Host "If clean — auxiliary move is safe."
Write-Host "If error — check which file is missing and move it back."