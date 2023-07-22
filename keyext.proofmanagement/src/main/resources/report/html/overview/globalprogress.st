<div style="width:100%; text-align:center">
    $if(cd.hasProvenContracts)$
    <div style="width: calc($proven$/$total$*100%); float:left;">proven</div>
    $endif$
    $if(cd.hasLemmaLeftContracts)$
    <div style="width: calc($lemmaLeft$/$total$*100%); float:left; white-space:nowrap;">dependencies left</div>
    $endif$
    $if(cd.hasUnprovenContracts)$
    <div style="width: calc($unproven$/$total$*100%); float:left;">unproven</div>
    $endif$
</div>
<div style="width:100%; background:#f1f1f1; color:white; text-align:center">
    $if(cd.hasProvenContracts)$
    <div style="width: calc($proven$/$total$*100%); background:#4CAF50; float:left;">$proven$</div>
    $endif$
    $if(cd.hasLemmaLeftContracts)$
    <div style="width: calc($lemmaLeft$/$total$*100%); background:#f48336; float:left;">$lemmaLeft$</div>
    $endif$
    $if(cd.hasUnprovenContracts)$
    <div style="width: calc($unproven$/$total$*100%); background:#f44336; float:left;">$unproven$</div>
    $endif$
</div>