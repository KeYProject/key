package org.key_project;

import javax.swing.*;
import java.util.function.Function;

public enum Actions {
    LOAD("load", "load a file to prove", c -> {

    }),
    LIST_PROOFS("list", "list all contracts", c -> {

    }),
    FILL("fill", "ask an oracle to fill in a missing contract", c -> {

    });


    public final String name;
    public final String helptext;
//    public final Function<Context, ActionResult> strategy;
    public final KeyAction strategy;
//    Actions(String name, String text, Function<Context, ActionResult> strategy) {
    Actions(String name, String text, KeyAction strategy) {
        this.name = name;
        this.helptext = text;
        this.strategy = strategy;
    }

    public void enact(Context c) {
        strategy.accept(c);
    }
}

