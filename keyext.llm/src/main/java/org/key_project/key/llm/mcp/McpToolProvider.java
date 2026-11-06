/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp;

import java.util.List;

/**
 * Bootstraps a set of {@link McpClient} instances from the service loader. Registered under
 * {@code META-INF/services/org.key_project.key.llm.mcp.McpToolProvider}.
 *
 * @author Alexander Weigl
 * @version 1 (28.06.26)
 */
public interface McpToolProvider {
    List<McpClient> get();
}
