package edu.kit.kastel.formal.mixfix;

import java.util.List;
// TODO: Auto-generated Javadoc
public class ParseContext<R, T> {

    private final MixFixParser<R, T> parser;
    private final List<T> tokenStream;
    private int curPos;
    private int maxBinding;
    private R result;

    public ParseContext(MixFixParser<R, T> parser, List<T> tokenStream) {
        this.tokenStream = tokenStream;
        this.parser = parser;
        this.maxBinding = Integer.MAX_VALUE;
    }

    private ParseContext(ParseContext<R,T> copyFrom) {
        this.parser = copyFrom.parser;
        this.curPos = copyFrom.curPos;
        this.tokenStream = copyFrom.tokenStream;
        this.maxBinding = copyFrom.maxBinding;
        this.result = copyFrom.result;
    }

    /**
     * @return the result
     */
    public R getResult() {
        return result;
    }

    // do not change last binding but keep it! -> for closed-rhs rules
    public ParseContext<R, T> setResult(R result) {
        ParseContext<R, T> res = new ParseContext<R, T>(this);
        res.result = result;
        return res;
    }

    public T getCurrentToken() {
        if (hasFinished()) {
            throw new IllegalStateException("Context already at its end");
        }

        return tokenStream.get(curPos);
    }

    public int getMaxBinding() {
        return maxBinding;
    }

    public ParseContext<R, T> setMaxBinding(int maxBinding) {
        ParseContext<R, T> res = new ParseContext<R, T>(this);
        res.maxBinding = maxBinding;
        return res;
    }

    public ParseContext<R, T> resetMaxBinding() {
        return setMaxBinding(Integer.MAX_VALUE);
    }

    public ADTList<ParseContext<R, T>> parseExpression(int minBinding) {
        // TODO Memoization of parsing results, with (curPos, minBinding and/or lastBinding)
        return parser.parseExpression(this, minBinding);
    }

    public ParseContext<R, T> consumeToken() {
        ParseContext<R, T> res = new ParseContext<R, T>(this);
        res.curPos++;
        return res;
    }

    public boolean hasFinished() {
        return curPos >= tokenStream.size();
    }

    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return "ParseContext [curPos=" + curPos + ", maxBinding=" + getMaxBinding()
                + ", result=" + result + "]";
    }

    public int getCurrentPosition() {
        return curPos;
    }


}
