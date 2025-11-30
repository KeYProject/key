<#-- @ftlvariable name="types" type="java.util.Collection<org.key_project.key.api.doc.Metamodel.Type>" -->
<#-- @ftlvariable name="endpoints" type="java.util.Collection<org.key_project.key.api.doc.Metamodel.Endpoint>" -->
<#-- @ftlvariable name="segmentDocumentation" type="java.util.Map<String,String>" -->

<html lang="en">
<head>
    <meta charset="utf-8">
    <link rel="stylesheet" href="https://keyproject.github.io/key-docs/assets/stylesheets/main.618322db.min.css"/>
    <link rel="stylesheet" href="https://keyproject.github.io/key-docs/assets/stylesheets/palette.ab4e12ef.min.css">
    <title></title>
</head>
<body>

<style>
    html {
        font-family: sans-serif;
        width: 60em;
        margin: auto;
    }

    div.data-type {
        span.kind {
            background: darkblue;
            color: white;
            padding: 1ex;
            font-size: 80%;
            border-radius: .3ex;
        }
    }

    div.data-type.enum {
        span.kind {
            background: darkgreen;
        }
    }

    .entry.field {
        padding-left: 2em;
    }

    h4 .async, h4 .sync {
        width: 10em;
        padding: .5ex;
        font-size: 80%;
        display: inline-block;
        background: lightcoral;
    }

    .direction {
        font-family: "Fira Code Light", monospace;
        margin-left: 5ex;
    }
</style>

<h3>Types</h3>
<#list types as type>
    <#assign isEnum = true>
    <#if type.fields??>
        <#assign isEnum = false>
    </#if>

    <div id="${type.name()}" class="data-type ${isEnum?string("enum","type")}">
        <h3>${type.name()} <span class="kind"> ${isEnum?string("enum","type")}</span></h3>
        <code class="highlight">
            <span class="k">${isEnum?string("enum","type")}</span>
            <span class="kc">${type.name()}</span> { <br/>
            <#if type.fields??>
                <#list type.fields as field>
                    <div class="entry field">
                        <#if field.documentation()??>
                            <div class="cm">/* ${field.documentation.text} */</div>
                        </#if>
                        <div><span class="kc">${field.type()}</span>&nbsp;<span
                                    class="nv">${field.name()}</span>;
                        </div>
                    </div>
                </#list>
            </#if>
            <#if type.values??>
                <#list type.values()?sort as value>
                    <#if value.documentation??>
                        /* ${value.documentation.text} */
                    </#if>
                    ${value.value()}
                </#list>
            </#if>
            }
        </code>
        <#if type.documentation??>
            <div class="documentation">
                <p>
                    ${type.documentation.text}
                </p>
                <ul>
                    <#list type.documentation.others as o>
                        <li><strong>${o.name}:</strong> ${o.value}</li>
                    </#list>
                </ul>
            </div>

            <#if (type.jsonExample)??>
                <div>
                    <details>
                        <summary>Example</summary>
                        <code class="highlight" style="white-space: pre">${type.jsonExample}</code>
                    </details>
                </div>
            </#if>
        </#if>
    </div>
</#list>


<h2 id="endpoints">Endpoints</h2>
<#assign lastSegment = "">
<div>
    <#list endpoints as ep>
        <#if lastSegment!=ep.segment()>
            <#assign lastSegment = ep.segment()>
            <h3 id="${lastSegment}">Segment: ${lastSegment}</h3>
            <#if segmentDocumentation[lastSegment]??>
                <#assign doc = segmentDocumentation[lastSegment]>
                <div class="documentation">
                    <p>
                        ${doc.text}
                    </p>
                    <ul>
                        <#list doc.others as o>
                            <li><strong>${o.name}:</strong> ${o.value}</li>
                        </#list>
                    </ul>
                </div>
            </#if>
        </#if>

        <div id="${ep.name()}" class="endpoint ${ep.isAsync()?string("async","sync")} ${ep.sender()}">
            <h4>
                <#if ep.isAsync()>
                    <span class="async">Notification:</span>
                <#else>
                    <span class="sync">Request:</span>
                </#if>
                ${ep.name()}
                <span class="direction">
                    <#if ep.sender() == "Server" && ep.isAsync()>
                        server ~~> client
                    <#elseif ep.sender() == "Server" && !ep.isAsync()>
                        server --> client
                    <#elseif ep.sender() == "Client" && !ep.isAsync()>
                        client --> server
                    <#elseif ep.sender() == "Client" && ep.isAsync()>
                        client ~~> server
                    </#if>
                </span>
            </h4>

            <code class="highlight">
                ${ep.name()}<span class="p">(</span>
                <#list ep.args() as arg>
                    <span class="kc">${arg.type}</span>
                    <span class="nv">${arg.name}</span><#sep><span class="p">,</span></#sep>
                </#list>
                <span class="p">)</span>
                <#if ep.returnType??>
                    <span class="p">:</span>
                    <span class="kc">${ep.returnType.identifier()}</span>
                </#if>
            </code>
            <#if ep.documentation??>
                <div class="documentation">
                    <p>
                        ${ep.documentation.text}
                    </p>
                    <ul>
                        <#list ep.documentation.others as o>
                            <li><strong>${o.name}:</strong> ${o.value}</li>
                        </#list>
                    </ul>
                </div>
            </#if>
        </div>
    </#list>
</div>

</body>
</html>
