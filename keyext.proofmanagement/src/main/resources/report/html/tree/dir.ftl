<span class="caret">${f}</span>
<ul class="nested active">
    <#list f.children as c>
        <@tree node=c />
    </#list>
</ul>
