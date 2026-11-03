
-- Added by the QRH MNF add-on v3 (scripts/mnf_prepare.sh): the MNF.RH library, the Sturm–Liouville file it uses, and its Comparator challenge.
lean_lib MNF where globs := #[`MNF.+]
lean_lib SturmLiouville where globs := #[`SturmLiouville.+]
lean_lib MNFChallenges where globs := #[`MNFChallenges.+]
