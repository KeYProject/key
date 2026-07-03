package org.key_project.key.llm.mcp;

import java.util.List;

/**
 * Demo implementation of an MCP client using type-safe record classes.
 *
 * @author Alexander Weigl
 * @version 1 (28.06.26)
 */
public class DemoMcpTool implements McpToolProvider, McpClient {
    @Override
    public List<McpClient> get() {
        return List.of(this);
    }

    @Override
    public List<Tool> getTools() {
        // Using the new type-safe record classes
        var echoTool = new Tool(new FunctionDefinition(
                "echo",
                "returns the given string",
                new JsonSchema("object")
        ));

        // Example with parameters
        var calculatorTool = new Tool(new FunctionDefinition(
                "calculate",
                "performs basic arithmetic operations",
                JsonSchema.builder()
                        .withType("object")
                        .addProperty("operation", JsonSchema.builder()
                                .withType("string")
                                .withDescription("The operation to perform (add, subtract, multiply, divide)")
                                .build())
                        .addProperty("a", JsonSchema.builder()
                                .withType("number")
                                .withDescription("First operand")
                                .build())
                        .addProperty("b", JsonSchema.builder()
                                .withType("number")
                                .withDescription("Second operand")
                                .build())
                        .addRequired("operation")
                        .addRequired("a")
                        .addRequired("b")
                        .build()
        ));
        return List.of(echoTool, calculatorTool);
    }

    @Override
    public Object callTool(String toolName, String arguments) {
        return null;
    }

    @Override
    public boolean isClosed() {
        return false;
    }

    @Override
    public void close() {
    }


}


