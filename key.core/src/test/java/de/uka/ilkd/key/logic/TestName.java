package de.uka.ilkd.key.logic;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class TestName {
    @Test
    public void testEquals() {
        Name n = new Name("test");
        Name m = new Name("test");
        assertEquals(n, m);
    }
}
