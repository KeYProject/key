<head>
<style type="text/css">
body, html {
    margin: 0;
    font-family: Arial;
}

.tab {
    overflow: hidden;
    background-color: #f1f1f1;
}

.tab button {
    background-color: inherit;
    float: left;
    border: none;
    outline: none;
    cursor: pointer;
    padding: 14px 16px;
    transition: 0.3s;
    font-size: 20px;
}

.tab button:hover {
    background-color: #ddd;
}

.tab button.active {
    background-color: #ccc
}

.tabcontent {
    display: none;
    padding: 6px 12px;

}

ul, #fileTree {
	list-style-type: none;
}

#fileTree {
	margin: 0;
	padding: 0;
}

.caret {
	cursor: pointer;
	user-select: none;
}

.caret::before {
	content: "\25B6";
	color: black;
	display: inline-block;
	margin-right: 6px;
}

.caret-down::before {
	transform: rotate(90deg);
}

.nested {
	display: none;
}

.active {
	display: block;
}

table {
    border-collapse: separate;
    border-spacing: 15px 15px;
}

tr:hover {
    background-color:#f5f5f5;
}

td, th {
    vertical-align: top;
    text-align: left;
}

</style>
</head>

<body>

<div class="tab">
    <button class="tablinks" onclick="openTab(event, 'overview')" id="defaultOpen">overview</button>
    <button class="tablinks" onclick="openTab(event, 'files')">files</button>
	<button class="tablinks" onclick="openTab(event, 'contracts')">contracts</button>
	<button class="tablinks" onclick="openTab(event, 'dependencies')">dependencies</button>
</div>

<div id="overview" class="tabcontent">
	<h3>Overview:</h3>
	<!-- TODO -->
    $/overview/overview(tree=treeRoot)$
</div>

<div id="files" class="tabcontent">
    <h3>Files found inside proof bundle:</h3>
	$/tree/tree(node=treeRoot)$
</div>

<div id="contracts" class="tabcontent">
    <h3>Contracts found inside proof bundle:</h3>
    $/lines/lines(contracts=lines)$
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
