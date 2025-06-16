<#-- @ftlvariable name="checkerData" type="org.key_project.proofmanagement.check.CheckerData" -->
<ul>
	<li>Bundle: ${checkerData.pbh.bundleName!"n/a"}</li>
	<li>Checks run:
      <#list checkerData.checks as c>
          ${c}<#if c_has_next>, </#if>
      </#list>
	</li>
	<li>Date: ${checkerData.checkDate}</li>
	<li>Overall Status: ${checkerData.globalState}</li>
	<li>Contracts:
      <@globalprogress
      data=cd
      total=checkerData.bundleProofCount
      proven=checkerData.provenCount
      lemmaLeft=checkerData.lemmaLeftCount
      unproven=checkerData.unprovenCount />
	</li>
	<li>Standard output:
		<div style="text-align:end;">
			<div>
				<input type="checkbox" id="errors" name="errors" value="[    Error    ]" onclick="handleClick(this)" checked>
				<label for="errors">Error</label>
				<input type="checkbox" id="warnings" name="warnings" value="[   Warning   ]" onclick="handleClick(this)"
				       checked>
				<label for="warnings">Warning</label>
				<input type="checkbox" id="info" name="info" value="[ Information ]" onclick="handleClick(this)" checked>
				<label for="info">Information</label>
				<input type="checkbox" id="debug" name="debug" value="[    Debug    ]" onclick="handleClick(this)" checked>
				<label for="debug">Debug</label>
			</div>
		</div>
		<div id="messages"
		     style="background-color:#002b36;
                    color:#93a1a1;
                    font-family:monospace;
                    font-size:16px;
                    width:max-content;
                    padding:10px">
        <#list checkerData.messages as msg>
            <#escape x as x?xml>
                ${msg}
            </#escape>
            <#if msg_has_next>
							<br/>
            </#if>
        </#list>
		</div>
	</li>
</ul>
