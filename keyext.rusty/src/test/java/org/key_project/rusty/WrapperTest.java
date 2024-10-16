package org.key_project.rusty;

import org.junit.jupiter.api.Test;
import org.key_project.rusty.nast.Wrapper;

public class WrapperTest {
    @Test
    void testWrapper() {
        var crate = Wrapper.parse();
        System.out.println(crate);
    }
}
