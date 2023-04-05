package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.util.LinkedHashMap;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (03.04.23)
 * @see KeyAst.ConfigurationFile#asConfiguration()
 */
class ConfigurationBuilder extends KeYParserBaseVisitor<Object> {
    private Configuration root;

    public Configuration getConfiguration() {
        return root;
    }

    @Override
    public List<Object> visitCfile(KeYParser.CfileContext ctx) {
        return ctx.cvalue().stream().map(it -> it.accept(this)).collect(Collectors.toList());
    }


    @Override
    public String visitCsymbol(KeYParser.CsymbolContext ctx) {
        return ctx.IDENT().getText();
    }

    @Override
    public String visitCstring(KeYParser.CstringContext ctx) {
        final var text = ctx.getText();
        return text.substring(1, text.length() - 1)
                .replace("\\\"", "\"")
                .replace("\\\\", "\\");
    }

    @Override
    public Object visitCintb(KeYParser.CintbContext ctx) {
        return Integer.parseInt(ctx.getText(), 2);
    }

    @Override
    public Object visitCinth(KeYParser.CinthContext ctx) {
        return Integer.parseInt(ctx.getText(), 16);
    }

    @Override
    public Object visitCintd(KeYParser.CintdContext ctx) {
        return Integer.parseInt(ctx.getText(), 10);
    }

    @Override
    public Object visitCfpf(KeYParser.CfpfContext ctx) {
        return Double.parseDouble(ctx.getText());
    }

    @Override
    public Object visitCfpd(KeYParser.CfpdContext ctx) {
        return Double.parseDouble(ctx.getText());
    }

    @Override
    public Object visitCfpr(KeYParser.CfprContext ctx) {
        return Double.parseDouble(ctx.getText());
    }

    @Override
    public Object visitCbool(KeYParser.CboolContext ctx) {
        return Boolean.parseBoolean(ctx.getText());
    }

    @Override
    public Object visitTable(KeYParser.TableContext ctx) {
        final var data = new LinkedHashMap<String, Object>();
        for (KeYParser.CkvContext context : ctx.ckv()) {
            var name = context.ckey().getText();
            var val = context.cvalue().accept(this);
            data.put(name, val);
        }
        return new Configuration(data);
    }

    @Override
    public Object visitList(KeYParser.ListContext ctx) {
        var seq = new ArrayList<>(ctx.children.size());
        for (KeYParser.CvalueContext context : ctx.cvalue()) {
            seq.add(context.accept(this));
        }
        return seq;
    }
}
