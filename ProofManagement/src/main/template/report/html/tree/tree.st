<ul id="fileTree">
    <li>
        $if(!node.children.empty)$
        $dir(f=node)$
        $else$
        $node$
        $endif$
    </li>
</ul>