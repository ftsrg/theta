// Generated from /home/levente/Documents/University/theta-refactor/subprojects/frontends/litmus2xcfa/src/main/antlr/BaseLexer.g4 by ANTLR 4.9.3
import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.TokenStream;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.misc.*;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class BaseLexer extends Lexer {
	static { RuntimeMetaData.checkVersion("4.9.3", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		Excl=1, Quot=2, Num=3, Dollar=4, Percent=5, Amp=6, Apos=7, LPar=8, RPar=9, 
		Ast=10, Plus=11, Comma=12, Minus=13, Period=14, Slash=15, Colon=16, Semi=17, 
		Less=18, Equals=19, Greater=20, Question=21, At=22, LBracket=23, RBracket=24, 
		BSlash=25, LBrace=26, RBrace=27, Circ=28, Tilde=29, Bar=30, Underscore=31;
	public static String[] channelNames = {
		"DEFAULT_TOKEN_CHANNEL", "HIDDEN"
	};

	public static String[] modeNames = {
		"DEFAULT_MODE"
	};

	private static String[] makeRuleNames() {
		return new String[] {
			"Excl", "Quot", "Num", "Dollar", "Percent", "Amp", "Apos", "LPar", "RPar", 
			"Ast", "Plus", "Comma", "Minus", "Period", "Slash", "Colon", "Semi", 
			"Less", "Equals", "Greater", "Question", "At", "LBracket", "RBracket", 
			"BSlash", "LBrace", "RBrace", "Circ", "Tilde", "Bar", "Underscore"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, "'!'", "'\"'", "'#'", "'$'", "'%'", "'&'", "'''", "'('", "')'", 
			"'*'", "'+'", "','", "'-'", "'.'", "'/'", "':'", "';'", "'<'", "'='", 
			"'>'", "'?'", "'@'", "'['", "']'", "'\\'", "'{'", "'}'", "'^'", "'~'", 
			"'|'", "'_'"
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, "Excl", "Quot", "Num", "Dollar", "Percent", "Amp", "Apos", "LPar", 
			"RPar", "Ast", "Plus", "Comma", "Minus", "Period", "Slash", "Colon", 
			"Semi", "Less", "Equals", "Greater", "Question", "At", "LBracket", "RBracket", 
			"BSlash", "LBrace", "RBrace", "Circ", "Tilde", "Bar", "Underscore"
		};
	}
	private static final String[] _SYMBOLIC_NAMES = makeSymbolicNames();
	public static final Vocabulary VOCABULARY = new VocabularyImpl(_LITERAL_NAMES, _SYMBOLIC_NAMES);

	/**
	 * @deprecated Use {@link #VOCABULARY} instead.
	 */
	@Deprecated
	public static final String[] tokenNames;
	static {
		tokenNames = new String[_SYMBOLIC_NAMES.length];
		for (int i = 0; i < tokenNames.length; i++) {
			tokenNames[i] = VOCABULARY.getLiteralName(i);
			if (tokenNames[i] == null) {
				tokenNames[i] = VOCABULARY.getSymbolicName(i);
			}

			if (tokenNames[i] == null) {
				tokenNames[i] = "<INVALID>";
			}
		}
	}

	@Override
	@Deprecated
	public String[] getTokenNames() {
		return tokenNames;
	}

	@Override

	public Vocabulary getVocabulary() {
		return VOCABULARY;
	}


	public BaseLexer(CharStream input) {
		super(input);
		_interp = new LexerATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	@Override
	public String getGrammarFileName() { return "BaseLexer.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public String[] getChannelNames() { return channelNames; }

	@Override
	public String[] getModeNames() { return modeNames; }

	@Override
	public ATN getATN() { return _ATN; }

	public static final String _serializedATN =
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\2!\177\b\1\4\2\t\2"+
		"\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4\13"+
		"\t\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\4\22\t\22"+
		"\4\23\t\23\4\24\t\24\4\25\t\25\4\26\t\26\4\27\t\27\4\30\t\30\4\31\t\31"+
		"\4\32\t\32\4\33\t\33\4\34\t\34\4\35\t\35\4\36\t\36\4\37\t\37\4 \t \3\2"+
		"\3\2\3\3\3\3\3\4\3\4\3\5\3\5\3\6\3\6\3\7\3\7\3\b\3\b\3\t\3\t\3\n\3\n\3"+
		"\13\3\13\3\f\3\f\3\r\3\r\3\16\3\16\3\17\3\17\3\20\3\20\3\21\3\21\3\22"+
		"\3\22\3\23\3\23\3\24\3\24\3\25\3\25\3\26\3\26\3\27\3\27\3\30\3\30\3\31"+
		"\3\31\3\32\3\32\3\33\3\33\3\34\3\34\3\35\3\35\3\36\3\36\3\37\3\37\3 \3"+
		" \2\2!\3\3\5\4\7\5\t\6\13\7\r\b\17\t\21\n\23\13\25\f\27\r\31\16\33\17"+
		"\35\20\37\21!\22#\23%\24\'\25)\26+\27-\30/\31\61\32\63\33\65\34\67\35"+
		"9\36;\37= ?!\3\2\2\2~\2\3\3\2\2\2\2\5\3\2\2\2\2\7\3\2\2\2\2\t\3\2\2\2"+
		"\2\13\3\2\2\2\2\r\3\2\2\2\2\17\3\2\2\2\2\21\3\2\2\2\2\23\3\2\2\2\2\25"+
		"\3\2\2\2\2\27\3\2\2\2\2\31\3\2\2\2\2\33\3\2\2\2\2\35\3\2\2\2\2\37\3\2"+
		"\2\2\2!\3\2\2\2\2#\3\2\2\2\2%\3\2\2\2\2\'\3\2\2\2\2)\3\2\2\2\2+\3\2\2"+
		"\2\2-\3\2\2\2\2/\3\2\2\2\2\61\3\2\2\2\2\63\3\2\2\2\2\65\3\2\2\2\2\67\3"+
		"\2\2\2\29\3\2\2\2\2;\3\2\2\2\2=\3\2\2\2\2?\3\2\2\2\3A\3\2\2\2\5C\3\2\2"+
		"\2\7E\3\2\2\2\tG\3\2\2\2\13I\3\2\2\2\rK\3\2\2\2\17M\3\2\2\2\21O\3\2\2"+
		"\2\23Q\3\2\2\2\25S\3\2\2\2\27U\3\2\2\2\31W\3\2\2\2\33Y\3\2\2\2\35[\3\2"+
		"\2\2\37]\3\2\2\2!_\3\2\2\2#a\3\2\2\2%c\3\2\2\2\'e\3\2\2\2)g\3\2\2\2+i"+
		"\3\2\2\2-k\3\2\2\2/m\3\2\2\2\61o\3\2\2\2\63q\3\2\2\2\65s\3\2\2\2\67u\3"+
		"\2\2\29w\3\2\2\2;y\3\2\2\2={\3\2\2\2?}\3\2\2\2AB\7#\2\2B\4\3\2\2\2CD\7"+
		"$\2\2D\6\3\2\2\2EF\7%\2\2F\b\3\2\2\2GH\7&\2\2H\n\3\2\2\2IJ\7\'\2\2J\f"+
		"\3\2\2\2KL\7(\2\2L\16\3\2\2\2MN\7)\2\2N\20\3\2\2\2OP\7*\2\2P\22\3\2\2"+
		"\2QR\7+\2\2R\24\3\2\2\2ST\7,\2\2T\26\3\2\2\2UV\7-\2\2V\30\3\2\2\2WX\7"+
		".\2\2X\32\3\2\2\2YZ\7/\2\2Z\34\3\2\2\2[\\\7\60\2\2\\\36\3\2\2\2]^\7\61"+
		"\2\2^ \3\2\2\2_`\7<\2\2`\"\3\2\2\2ab\7=\2\2b$\3\2\2\2cd\7>\2\2d&\3\2\2"+
		"\2ef\7?\2\2f(\3\2\2\2gh\7@\2\2h*\3\2\2\2ij\7A\2\2j,\3\2\2\2kl\7B\2\2l"+
		".\3\2\2\2mn\7]\2\2n\60\3\2\2\2op\7_\2\2p\62\3\2\2\2qr\7^\2\2r\64\3\2\2"+
		"\2st\7}\2\2t\66\3\2\2\2uv\7\177\2\2v8\3\2\2\2wx\7`\2\2x:\3\2\2\2yz\7\u0080"+
		"\2\2z<\3\2\2\2{|\7~\2\2|>\3\2\2\2}~\7a\2\2~@\3\2\2\2\3\2\2";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}