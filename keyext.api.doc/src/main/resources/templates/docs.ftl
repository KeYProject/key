<#-- @ftlvariable name="types" type="java.util.Collection<org.key_project.key.api.doc.Metamodel.Type>" -->
<#-- @ftlvariable name="endpoints" type="java.util.Collection<org.key_project.key.api.doc.Metamodel.Endpoint>" -->
<#-- @ftlvariable name="segmentDocumentation" type="java.util.Map<String,String>" -->
<#-- @ftlvariable name="endpointsBySegment" type="java.util.Map<String, java.util.List<org.key_project.key.api.doc.Metamodel.Endpoint>>" -->

<html lang="en">
<head>
	<meta charset="utf-8">
	<title>KeY API Documentation</title>
</head>
<body>

<style>
    html {
        font-family: "Roboto", sans-serif;
        font-size: 12pt;
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

    body {
        margin: 0;
    }

    #main {
        display: grid;
        grid-template-columns: 15% 70%;
        gap: 1%;
    }

    #nav {
        padding: 0em 1em 0em 1em;
        background: #444;
        color: white;
        font-size: 80%;

        a {
            color: white;
        }

        ul {

        }

        li {
        }
    }

    #content {
        padding: 0em 1em 0em 1em;
    }

    .highlight {
        background: #ddd;
        font-family: "Fira Code Light", monospace;
        padding: 1ex;

		    .entry{
				    margin-top: 1ex;
		    }
        .k {
            font-weight: bold;
            color: darkviolet;
        }

        .cm {
            color: darkgreen;
		        font-style: italic;
        }

        .kc {
            color: blue;
        }


    }
</style>

<div id="main">
	<nav id="nav">
		<h1>Documentation: KeY JSON-RPC API</h1>

		<div>
			Version: ${version}<br>
			Date: ${date}
		</div>

		<h2>Types</h2>

		<ul>
        <#list types as type>
					<li><a href="#${type.name}">${type.name()}</a></li>
        </#list>
		</ul>

		<h2>Procedures</h2>
		<ul>
        <#list endpointsBySegment as segname, seq>
					<li><abbr title="${(segmentDocumentation[segname].text)!"n/a"}">${segname}</abbr>
						<ul>
                <#list seq as ep>
									<li><a href="#${ep.name}">${ep.name()}</a></li>
                </#list>
						</ul>
					</li>
        </#list>
		</ul>
	</nav>
	<div id="content">
		<h2>Base Definitions</h2>
		<p>
			This API builds upon and uses the same convention as the <a
							href="https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/">Language
				Server Protocol</a>.
			In basic, the protocol builds upon a simple HTTP protocol with a JSON playoad. A request message looks as
		</p>
		<div class="highlight"><pre>Content-Length: 80\r\n
Content-Type: application/vscode-jsonrpc; charset=utf-8\r\n
\r\n
{
	"jsonrpc": "2.0",
	"id": 1,
	"method": "env/version",
	"params": {
		...
	}
}</pre></div>
		<p>
			Header <code>Content-Type</code> is optional. The <code>\r\n</code> are mandatory. The field <code>id</code> make
			the difference between a request or a notification. Later do not result into a response. A response message
			contains the fields <code>result</code> or <code>error</code>, depending on a normal or exceptional execution of
			the request.
		</p>
		<p>
			The communication is always asynchronous and duplex. Meaning you can send and receive messages at any time.
			For synchronous calls, the client and server library need to implement a waiting mechanism.
		</p>


		<h2>Types</h2>
		<div class="data-type">
        <#list types as type>
            <#assign isEnum = true>
            <#if type.fields??>
                <#assign isEnum = false>
            </#if>

					<div id="${type.name()}" class="data-type ${isEnum?string("enum","type")}">
						<h3>${type.name()} <span class="kind"> ${isEnum?string("enum","type")}</span></h3>
						<div class="highlight">
							<span class="k">${isEnum?string("enum","type")}</span>
							<span class="kc"><a href="#${type.name()}">${type.name()}</a></span> { <br/>
                <#if type.fields??>
                    <#list type.fields as field>
											<div class="entry field">
                          <#if field.documentation()??>
														<div class="cm">/* ${field.documentation.text} */</div>
                          </#if>
												<div><span class="kc"><a href="#${type.name()}">${type.name()}</a></span>&nbsp;<span
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
						</div>
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
		</div>

		<h2 id="endpoints">Endpoints</h2>
      <#assign lastSegment = "">
		<div class="endpoints">
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
	                <span class="kc"><a href="#${arg.type}">${arg.type}</a></span>
									<span class="nv">${arg.name}</span><#sep><span class="p">,</span></#sep>
                </#list>
							<span class="p">)</span>
                <#if ep.returnType??>
									<span class="p">:</span>
	                <span class="kc"><a href="#${ep.returnType.name()}">${ep.returnType.name()}</a></span>
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
	</div>
</div>
</body>
</html>
