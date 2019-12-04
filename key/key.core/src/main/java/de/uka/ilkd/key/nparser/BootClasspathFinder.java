package de.uka.ilkd.key.nparser;

import org.jetbrains.annotations.Nullable;

/**
 * @author Alexander Weigl
 * @version 1 (12/4/19)
 */
public class BootClasspathFinder extends AbstractBuilder<Void> {

    private @Nullable String bootClasspath;

    @Override
    public Void visitBootClassPath(KeYParser.BootClassPathContext ctx) {
        bootClasspath = ParsingFacade.getValue(ctx.string_value());
        return null;
    }

    public String getBootClasspath() {
        return bootClasspath;
    }
}
