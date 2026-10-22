# patches/ -- the owners' edits of the frozen source for the artifact evaluation

One file per lane and topic, `NN-<lane>-<topic>.patch`, made with `git diff` (or `git format-patch`) against
`b0eb75189` in that commit's own paths and names (before the rename). `rederive.sh` applies them in name order with
`git apply --index`, before anything else; one that does not apply stops the derivation.

The header (the lines before the first `diff --git`) names the survey rows the patch closes, by `survey.tsv` path and
item. The owner builds `b0eb75189` with the patch applied, as their own check. A patch removes or rewrites
development material only; the output check (`check-trees.sh`) must find every emitted tree unchanged.
