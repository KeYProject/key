<head>
    <meta charset="UTF-8">
    <title>$title$</title>
    <style type="text/css">
        $style()$
    </style>
    $scripts()$
</head>

<body>

<div class="tab">
    <button class="tablinks" onclick="openTab(event, 'overview')" id="defaultOpen">Overview</button>
    <button class="tablinks" onclick="openTab(event, 'files')">Files</button>
	<button class="tablinks" onclick="openTab(event, 'contracts')">Contracts</button>
	<button class="tablinks" onclick="openTab(event, 'dependencies')">Dependencies</button>
</div>

<div id="overview" class="tabcontent">
$/overview/overview(cd=checkerData)$
</div>

<div id="files" class="tabcontent">
    <h3>Files found inside proof bundle:</h3>
	$/tree/tree(node=treeRoot)$
</div>

<div id="contracts" class="tabcontent">
    <h3>Contracts with proof inside bundle:</h3>
    $/lines/lines(cd=checkerData, entries=entries)$
    <h3>Contracts declared inside bundle without proof:</h3>
    $/lines/prooflessContracts(cd=checkerData)$
    <h3>Settings comparison:</h3>
    $/settings/settings(cd=checkerData)$
</div>

<div id="dependencies" class="tabcontent">
    <h3>Dependencies between contracts:</h3>
    $if(graph)$
        $/dependency/dependencies(graph=graph)$
    $else$
        Dependency check has not been enabled. Use <code>--dependency</code> flag to enable it.
    $endif$
</div>

<script type="text/javascript">
// make the filetree foldable/expandable
let toggler = document.getElementsByClassName("caret");
for (let i = 0; i < toggler.length; i++) {
	toggler[i].addEventListener("click", function() {
		this.parentElement.querySelector(".nested").classList.toggle("active");
		this.classList.toggle("caret-down");
	});
}

// ensure that the overview tab is opened when the file is loaded
document.getElementById("defaultOpen").click()
</script>

</body>
