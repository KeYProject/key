
package java.util;

import java.io.Serializable;
import java.text.NumberFormat;

public final class Currency implements Serializable {
    static final long serialVersionUID = -158308464356906721L;
    private Currency() {}

    private Currency(Locale loc) {}
    public String getCurrencyCode() {}
    public int getDefaultFractionDigits() {}
    public static Currency getInstance(Locale locale) {}
    public static Currency getInstance(String currencyCode) {}
    public String getSymbol() {}
    public String getSymbol(Locale locale) {}
    public String toString() {}
}
