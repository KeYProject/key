<head>
    <style type="text/css">
        $style()$
    </style>
</head>

<body>

<div class="tab">
    <button class="tablinks" onclick="openTab(event, 'overview')" id="defaultOpen">Overview</button>
    <button class="tablinks" onclick="openTab(event, 'files')">Files</button>
	<button class="tablinks" onclick="openTab(event, 'contracts')">Contracts</button>
	<button class="tablinks" onclick="openTab(event, 'dependencies')">Dependencies</button>
</div>

<div id="overview" class="tabcontent">
    $/overview/overview(cd=checkerData, dataView=dataView)$
</div>

<div id="files" class="tabcontent">
    <h3>Files found inside proof bundle:</h3>
	$/tree/tree(node=treeRoot)$
</div>

<div id="contracts" class="tabcontent">
    <h3>Contracts found inside proof bundle:</h3>
    $/lines/lines(dataView=dataView, contracts=lines)$
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
function openTab(evt, tabName) {
    var i, tabcontent, tablinks;

    tabcontent = document.getElementsByClassName("tabcontent");
    for (i = 0; i < tabcontent.length; i++) {
        tabcontent[i].style.display = "none";
    }

    tablinks = document.getElementsByClassName("tablinks");
    for (i = 0; i < tablinks.length; i++) {
        tablinks[i].className = tablinks[i].className.replace(" active", "");
    }

    document.getElementById(tabName).style.display = "block";
    evt.currentTarget.className += " active";
}

document.getElementById("defaultOpen").click()

var toggler = document.getElementsByClassName("caret");
var i;

for (i = 0; i < toggler.length; i++) {
	toggler[i].addEventListener("click", function() {
		this.parentElement.querySelector(".nested").classList.toggle("active");
		this.classList.toggle("caret-down");
	});
}
</script>
</body>
