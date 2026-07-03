package org.key_project.key.llm.mcp;

import java.util.List;

/**
 *
 * @author Alexander Weigl
 * @version 1 (28.06.26)
 */
interface McpToolProvider {
    List<McpClient> get();
}
