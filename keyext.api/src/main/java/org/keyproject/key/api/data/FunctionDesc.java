package org.keyproject.key.api.data;

import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (15.10.23)
 */
public record FunctionDesc(String name, String sort, List<String> sorts) {
}
