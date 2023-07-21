    <ul>
        <li>Bundle: $cd.Pbh.bundleName$</li>
        <li>Checks run: $cd.checks:{c | $c$}; separator=", "$</li>
        <li>Date: $cd.checkDate$</li>
        <li>Overall Status: $cd.globalState$</li>
        <li>Contracts:
            $globalprogress(data=cd,
                            total=cd.bundleProofCount,
                            proven=cd.provenCount,
                            lemmaLeft=cd.lemmaLeftCount,
                            unproven=cd.unprovenCount)$
        </li>
        <li>Standard output:
            <div style="text-align:end;">
                <div>
                    <input type="checkbox" id="errors" name="errors" value="[    Error    ]" onclick="handleClick(this)" checked>
                    <label for="errors">Error</label>
                    <input type="checkbox" id="warnings" name="warnings" value="[   Warning   ]" onclick="handleClick(this)" checked>
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
<span>$cd.messages; separator={</span>$\n$<span>}, format="xml-encode"$</span>
            </div>
        </li>
    </ul>
