<ul id="fileTree">
	<li>
      <#if node.children?has_content>
          <@dir f=node />
      <#else>
          ${node}
      </#if>
	</li>
</ul>
