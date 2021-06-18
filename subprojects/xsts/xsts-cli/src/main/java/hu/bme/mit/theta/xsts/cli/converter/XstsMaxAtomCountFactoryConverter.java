package hu.bme.mit.theta.xsts.cli.converter;

import com.beust.jcommander.IStringConverter;
import hu.bme.mit.theta.xsts.analysis.maxatomcount.*;

public class XstsMaxAtomCountFactoryConverter implements IStringConverter<XstsMaxAtomCountFactory> {
    @Override
    public XstsMaxAtomCountFactory convert(String value) {
        switch (value) {
            case "UNLIMITED":
                return new XstsUnlimitedMaxAtomCountFactory();
            case "ALLASSUMES":
                return new XstsAllAssumesMaxAtomCountFactory();
            case "ALLEXPRS":
                return new XstsAllExprsMaxAtomCountFactory();
            default:
                final int n = Integer.parseInt(value);
                return new XstsNMaxAtomCountFactory(n);
        }
    }
}
