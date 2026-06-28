package org.key_project.key.llm.mcp;

import org.jspecify.annotations.NullMarked;

import java.util.List;
import java.util.ServiceLoader;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;

/**
 *
 * @author Alexander Weigl
 * @version 1 (28.06.26)
 */
@NullMarked
public class BuiltInMCPClient implements McpClient {
    private final Set<String> allowedToolsWithApproval = new TreeSet<>();
    private final Set<String> allowedToolsWithoutApproval = new TreeSet<>();

    private final List<McpClient> tools;
    private boolean isClosed = false;

    public BuiltInMCPClient() {
        var loader = ServiceLoader.load(McpToolProvider.class);
        tools = loader.stream().flatMap(it -> it.get().get().stream()).toList();
    }

    public Set<String> getAllowedToolsWithApproval() {
        return allowedToolsWithApproval;
    }

    public Set<String> getAllowedToolsWithoutApproval() {
        return allowedToolsWithoutApproval;
    }

    public Set<String> getAllToolNames() {
        return tools.stream().flatMap(it -> it.getTools().stream())
                .map(it -> it.function().name())
                .collect(Collectors.toCollection(TreeSet::new));
    }


    @Override
    public List<Tool> getTools() {
        var allowedTools = new TreeSet<>(allowedToolsWithApproval);
        allowedToolsWithoutApproval.addAll(allowedTools);
        return tools.stream().flatMap(it -> it.getTools().stream())
                .filter(it -> allowedTools.contains(it.function().name()))
                .toList();
    }

    @Override
    public Object callTool(String toolName, String arguments) throws McpToolNowAllowedException {
        if (!allowedToolsWithApproval.contains(toolName) &&
                !allowedToolsWithoutApproval.contains(toolName)) {
            throw new McpToolNowAllowedException();
        }

        System.out.println("Calling tool " + toolName + " with arguments " + arguments);
        return new Object();
    }

    @Override
    public boolean isClosed() {
        return isClosed;
    }

    @Override
    public void close() {
        isClosed = true;
    }
}
