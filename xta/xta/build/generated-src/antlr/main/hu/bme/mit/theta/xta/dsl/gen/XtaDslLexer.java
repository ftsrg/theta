// Generated from XtaDsl.g4 by ANTLR 4.7.2
package hu.bme.mit.theta.xta.dsl.gen;
import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.TokenStream;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.misc.*;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class XtaDslLexer extends Lexer {
	static { RuntimeMetaData.checkVersion("4.7.2", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		SYSTEM=1, PROCESS=2, STATE=3, COMMIT=4, URGENT=5, INIT=6, TRANS=7, SELECT=8, 
		GUARD=9, SYNC=10, ASSIGN=11, TYPEDEF=12, VOID=13, INT=14, CLOCK=15, CHAN=16, 
		BOOL=17, SCALAR=18, STRUCT=19, BROADCAST=20, CONST=21, FOR=22, WHILE=23, 
		DO=24, IF=25, ELSE=26, RETURN=27, FORALL=28, EXISTS=29, OR=30, IMPLY=31, 
		AND=32, NOT=33, LOGOROP=34, LOGANDOP=35, SHLOP=36, SHROP=37, EQOP=38, 
		NEQOP=39, NEWASSIGNOP=40, OLDASSIGNOP=41, ADDASSIGNOP=42, SUBASSIGNOP=43, 
		MULASSIGNOP=44, DIVASSIGNOP=45, REMASSIGNOP=46, BWORASSIGNOP=47, BWANDASSIGNOP=48, 
		BWXORASSIGNOP=49, SHLASSIGNOP=50, SHRASSIGNOP=51, LTOP=52, LEQOP=53, GTOP=54, 
		GEQOP=55, INCOP=56, DECOP=57, TRUE=58, FALSE=59, NAT=60, DOT=61, ID=62, 
		UNDERSCORE=63, DIGIT=64, LETTER=65, LPAREN=66, RPAREN=67, LBRACK=68, RBRACK=69, 
		LBRAC=70, RBRAC=71, COMMA=72, COLON=73, SEMICOLON=74, AMP=75, HAT=76, 
		BAR=77, EXCL=78, QUEST=79, PERCENT=80, PLUS=81, MINUS=82, ASTER=83, SLASH=84, 
		TILDE=85, LARROW=86, RARROW=87, WS=88, COMMENT=89, LINE_COMMENT=90;
	public static String[] channelNames = {
		"DEFAULT_TOKEN_CHANNEL", "HIDDEN"
	};

	public static String[] modeNames = {
		"DEFAULT_MODE"
	};

	private static String[] makeRuleNames() {
		return new String[] {
			"SYSTEM", "PROCESS", "STATE", "COMMIT", "URGENT", "INIT", "TRANS", "SELECT", 
			"GUARD", "SYNC", "ASSIGN", "TYPEDEF", "VOID", "INT", "CLOCK", "CHAN", 
			"BOOL", "SCALAR", "STRUCT", "BROADCAST", "CONST", "FOR", "WHILE", "DO", 
			"IF", "ELSE", "RETURN", "FORALL", "EXISTS", "OR", "IMPLY", "AND", "NOT", 
			"LOGOROP", "LOGANDOP", "SHLOP", "SHROP", "EQOP", "NEQOP", "NEWASSIGNOP", 
			"OLDASSIGNOP", "ADDASSIGNOP", "SUBASSIGNOP", "MULASSIGNOP", "DIVASSIGNOP", 
			"REMASSIGNOP", "BWORASSIGNOP", "BWANDASSIGNOP", "BWXORASSIGNOP", "SHLASSIGNOP", 
			"SHRASSIGNOP", "LTOP", "LEQOP", "GTOP", "GEQOP", "INCOP", "DECOP", "TRUE", 
			"FALSE", "NAT", "DOT", "ID", "UNDERSCORE", "DIGIT", "LETTER", "LPAREN", 
			"RPAREN", "LBRACK", "RBRACK", "LBRAC", "RBRAC", "COMMA", "COLON", "SEMICOLON", 
			"AMP", "HAT", "BAR", "EXCL", "QUEST", "PERCENT", "PLUS", "MINUS", "ASTER", 
			"SLASH", "TILDE", "LARROW", "RARROW", "WS", "COMMENT", "LINE_COMMENT"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, "'system'", "'process'", "'state'", "'commit'", "'urgent'", "'init'", 
			"'trans'", "'select'", "'guard'", "'sync'", "'assign'", "'typedef'", 
			"'void'", "'int'", "'clock'", "'chan'", "'bool'", "'scalar'", "'struct'", 
			"'broadcast'", "'const'", "'for'", "'while'", "'do'", "'if'", "'else'", 
			"'return'", "'forall'", "'exists'", "'or'", "'imply'", "'and'", "'not'", 
			"'||'", "'&&'", "'<<'", "'>>'", "'=='", "'!='", "'='", "':='", "'+='", 
			"'-='", "'*='", "'/='", "'%='", "'|='", "'&='", "'^='", "'<<='", "'>>='", 
			"'<'", "'<='", "'>'", "'>='", "'++'", "'--'", "'true'", "'false'", null, 
			"'.'", null, "'_'", null, null, "'('", "')'", "'['", "']'", "'{'", "'}'", 
			"','", "':'", "';'", "'&'", "'^'", "'|'", "'!'", "'?'", "'%'", "'+'", 
			"'-'", "'*'", "'/'", "'~'", "'<-'", "'->'"
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, "SYSTEM", "PROCESS", "STATE", "COMMIT", "URGENT", "INIT", "TRANS", 
			"SELECT", "GUARD", "SYNC", "ASSIGN", "TYPEDEF", "VOID", "INT", "CLOCK", 
			"CHAN", "BOOL", "SCALAR", "STRUCT", "BROADCAST", "CONST", "FOR", "WHILE", 
			"DO", "IF", "ELSE", "RETURN", "FORALL", "EXISTS", "OR", "IMPLY", "AND", 
			"NOT", "LOGOROP", "LOGANDOP", "SHLOP", "SHROP", "EQOP", "NEQOP", "NEWASSIGNOP", 
			"OLDASSIGNOP", "ADDASSIGNOP", "SUBASSIGNOP", "MULASSIGNOP", "DIVASSIGNOP", 
			"REMASSIGNOP", "BWORASSIGNOP", "BWANDASSIGNOP", "BWXORASSIGNOP", "SHLASSIGNOP", 
			"SHRASSIGNOP", "LTOP", "LEQOP", "GTOP", "GEQOP", "INCOP", "DECOP", "TRUE", 
			"FALSE", "NAT", "DOT", "ID", "UNDERSCORE", "DIGIT", "LETTER", "LPAREN", 
			"RPAREN", "LBRACK", "RBRACK", "LBRAC", "RBRAC", "COMMA", "COLON", "SEMICOLON", 
			"AMP", "HAT", "BAR", "EXCL", "QUEST", "PERCENT", "PLUS", "MINUS", "ASTER", 
			"SLASH", "TILDE", "LARROW", "RARROW", "WS", "COMMENT", "LINE_COMMENT"
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


	public XtaDslLexer(CharStream input) {
		super(input);
		_interp = new LexerATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	@Override
	public String getGrammarFileName() { return "XtaDsl.g4"; }

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
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\2\\\u0231\b\1\4\2\t"+
		"\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4\13"+
		"\t\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\4\22\t\22"+
		"\4\23\t\23\4\24\t\24\4\25\t\25\4\26\t\26\4\27\t\27\4\30\t\30\4\31\t\31"+
		"\4\32\t\32\4\33\t\33\4\34\t\34\4\35\t\35\4\36\t\36\4\37\t\37\4 \t \4!"+
		"\t!\4\"\t\"\4#\t#\4$\t$\4%\t%\4&\t&\4\'\t\'\4(\t(\4)\t)\4*\t*\4+\t+\4"+
		",\t,\4-\t-\4.\t.\4/\t/\4\60\t\60\4\61\t\61\4\62\t\62\4\63\t\63\4\64\t"+
		"\64\4\65\t\65\4\66\t\66\4\67\t\67\48\t8\49\t9\4:\t:\4;\t;\4<\t<\4=\t="+
		"\4>\t>\4?\t?\4@\t@\4A\tA\4B\tB\4C\tC\4D\tD\4E\tE\4F\tF\4G\tG\4H\tH\4I"+
		"\tI\4J\tJ\4K\tK\4L\tL\4M\tM\4N\tN\4O\tO\4P\tP\4Q\tQ\4R\tR\4S\tS\4T\tT"+
		"\4U\tU\4V\tV\4W\tW\4X\tX\4Y\tY\4Z\tZ\4[\t[\3\2\3\2\3\2\3\2\3\2\3\2\3\2"+
		"\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\4\3\4\3\4\3\4\3\4\3\4\3\5\3\5\3\5\3"+
		"\5\3\5\3\5\3\5\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\7\3\7\3\7\3\7\3\7\3\b\3\b"+
		"\3\b\3\b\3\b\3\b\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\n\3\n\3\n\3\n\3\n\3\n\3"+
		"\13\3\13\3\13\3\13\3\13\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\r\3\r\3\r\3\r\3"+
		"\r\3\r\3\r\3\r\3\16\3\16\3\16\3\16\3\16\3\17\3\17\3\17\3\17\3\20\3\20"+
		"\3\20\3\20\3\20\3\20\3\21\3\21\3\21\3\21\3\21\3\22\3\22\3\22\3\22\3\22"+
		"\3\23\3\23\3\23\3\23\3\23\3\23\3\23\3\24\3\24\3\24\3\24\3\24\3\24\3\24"+
		"\3\25\3\25\3\25\3\25\3\25\3\25\3\25\3\25\3\25\3\25\3\26\3\26\3\26\3\26"+
		"\3\26\3\26\3\27\3\27\3\27\3\27\3\30\3\30\3\30\3\30\3\30\3\30\3\31\3\31"+
		"\3\31\3\32\3\32\3\32\3\33\3\33\3\33\3\33\3\33\3\34\3\34\3\34\3\34\3\34"+
		"\3\34\3\34\3\35\3\35\3\35\3\35\3\35\3\35\3\35\3\36\3\36\3\36\3\36\3\36"+
		"\3\36\3\36\3\37\3\37\3\37\3 \3 \3 \3 \3 \3 \3!\3!\3!\3!\3\"\3\"\3\"\3"+
		"\"\3#\3#\3#\3$\3$\3$\3%\3%\3%\3&\3&\3&\3\'\3\'\3\'\3(\3(\3(\3)\3)\3*\3"+
		"*\3*\3+\3+\3+\3,\3,\3,\3-\3-\3-\3.\3.\3.\3/\3/\3/\3\60\3\60\3\60\3\61"+
		"\3\61\3\61\3\62\3\62\3\62\3\63\3\63\3\63\3\63\3\64\3\64\3\64\3\64\3\65"+
		"\3\65\3\66\3\66\3\66\3\67\3\67\38\38\38\39\39\39\3:\3:\3:\3;\3;\3;\3;"+
		"\3;\3<\3<\3<\3<\3<\3<\3=\6=\u01cc\n=\r=\16=\u01cd\3>\3>\3?\3?\5?\u01d4"+
		"\n?\3?\3?\3?\7?\u01d9\n?\f?\16?\u01dc\13?\3@\3@\3A\3A\3B\3B\3C\3C\3D\3"+
		"D\3E\3E\3F\3F\3G\3G\3H\3H\3I\3I\3J\3J\3K\3K\3L\3L\3M\3M\3N\3N\3O\3O\3"+
		"P\3P\3Q\3Q\3R\3R\3S\3S\3T\3T\3U\3U\3V\3V\3W\3W\3W\3X\3X\3X\3Y\6Y\u0213"+
		"\nY\rY\16Y\u0214\3Y\3Y\3Z\3Z\3Z\3Z\7Z\u021d\nZ\fZ\16Z\u0220\13Z\3Z\3Z"+
		"\3Z\3Z\3Z\3[\3[\3[\3[\7[\u022b\n[\f[\16[\u022e\13[\3[\3[\3\u021e\2\\\3"+
		"\3\5\4\7\5\t\6\13\7\r\b\17\t\21\n\23\13\25\f\27\r\31\16\33\17\35\20\37"+
		"\21!\22#\23%\24\'\25)\26+\27-\30/\31\61\32\63\33\65\34\67\359\36;\37="+
		" ?!A\"C#E$G%I&K\'M(O)Q*S+U,W-Y.[/]\60_\61a\62c\63e\64g\65i\66k\67m8o9"+
		"q:s;u<w=y>{?}@\177A\u0081B\u0083C\u0085D\u0087E\u0089F\u008bG\u008dH\u008f"+
		"I\u0091J\u0093K\u0095L\u0097M\u0099N\u009bO\u009dP\u009fQ\u00a1R\u00a3"+
		"S\u00a5T\u00a7U\u00a9V\u00abW\u00adX\u00afY\u00b1Z\u00b3[\u00b5\\\3\2"+
		"\6\3\2\62;\4\2C\\c|\5\2\13\f\16\17\"\"\4\2\f\f\17\17\2\u0238\2\3\3\2\2"+
		"\2\2\5\3\2\2\2\2\7\3\2\2\2\2\t\3\2\2\2\2\13\3\2\2\2\2\r\3\2\2\2\2\17\3"+
		"\2\2\2\2\21\3\2\2\2\2\23\3\2\2\2\2\25\3\2\2\2\2\27\3\2\2\2\2\31\3\2\2"+
		"\2\2\33\3\2\2\2\2\35\3\2\2\2\2\37\3\2\2\2\2!\3\2\2\2\2#\3\2\2\2\2%\3\2"+
		"\2\2\2\'\3\2\2\2\2)\3\2\2\2\2+\3\2\2\2\2-\3\2\2\2\2/\3\2\2\2\2\61\3\2"+
		"\2\2\2\63\3\2\2\2\2\65\3\2\2\2\2\67\3\2\2\2\29\3\2\2\2\2;\3\2\2\2\2=\3"+
		"\2\2\2\2?\3\2\2\2\2A\3\2\2\2\2C\3\2\2\2\2E\3\2\2\2\2G\3\2\2\2\2I\3\2\2"+
		"\2\2K\3\2\2\2\2M\3\2\2\2\2O\3\2\2\2\2Q\3\2\2\2\2S\3\2\2\2\2U\3\2\2\2\2"+
		"W\3\2\2\2\2Y\3\2\2\2\2[\3\2\2\2\2]\3\2\2\2\2_\3\2\2\2\2a\3\2\2\2\2c\3"+
		"\2\2\2\2e\3\2\2\2\2g\3\2\2\2\2i\3\2\2\2\2k\3\2\2\2\2m\3\2\2\2\2o\3\2\2"+
		"\2\2q\3\2\2\2\2s\3\2\2\2\2u\3\2\2\2\2w\3\2\2\2\2y\3\2\2\2\2{\3\2\2\2\2"+
		"}\3\2\2\2\2\177\3\2\2\2\2\u0081\3\2\2\2\2\u0083\3\2\2\2\2\u0085\3\2\2"+
		"\2\2\u0087\3\2\2\2\2\u0089\3\2\2\2\2\u008b\3\2\2\2\2\u008d\3\2\2\2\2\u008f"+
		"\3\2\2\2\2\u0091\3\2\2\2\2\u0093\3\2\2\2\2\u0095\3\2\2\2\2\u0097\3\2\2"+
		"\2\2\u0099\3\2\2\2\2\u009b\3\2\2\2\2\u009d\3\2\2\2\2\u009f\3\2\2\2\2\u00a1"+
		"\3\2\2\2\2\u00a3\3\2\2\2\2\u00a5\3\2\2\2\2\u00a7\3\2\2\2\2\u00a9\3\2\2"+
		"\2\2\u00ab\3\2\2\2\2\u00ad\3\2\2\2\2\u00af\3\2\2\2\2\u00b1\3\2\2\2\2\u00b3"+
		"\3\2\2\2\2\u00b5\3\2\2\2\3\u00b7\3\2\2\2\5\u00be\3\2\2\2\7\u00c6\3\2\2"+
		"\2\t\u00cc\3\2\2\2\13\u00d3\3\2\2\2\r\u00da\3\2\2\2\17\u00df\3\2\2\2\21"+
		"\u00e5\3\2\2\2\23\u00ec\3\2\2\2\25\u00f2\3\2\2\2\27\u00f7\3\2\2\2\31\u00fe"+
		"\3\2\2\2\33\u0106\3\2\2\2\35\u010b\3\2\2\2\37\u010f\3\2\2\2!\u0115\3\2"+
		"\2\2#\u011a\3\2\2\2%\u011f\3\2\2\2\'\u0126\3\2\2\2)\u012d\3\2\2\2+\u0137"+
		"\3\2\2\2-\u013d\3\2\2\2/\u0141\3\2\2\2\61\u0147\3\2\2\2\63\u014a\3\2\2"+
		"\2\65\u014d\3\2\2\2\67\u0152\3\2\2\29\u0159\3\2\2\2;\u0160\3\2\2\2=\u0167"+
		"\3\2\2\2?\u016a\3\2\2\2A\u0170\3\2\2\2C\u0174\3\2\2\2E\u0178\3\2\2\2G"+
		"\u017b\3\2\2\2I\u017e\3\2\2\2K\u0181\3\2\2\2M\u0184\3\2\2\2O\u0187\3\2"+
		"\2\2Q\u018a\3\2\2\2S\u018c\3\2\2\2U\u018f\3\2\2\2W\u0192\3\2\2\2Y\u0195"+
		"\3\2\2\2[\u0198\3\2\2\2]\u019b\3\2\2\2_\u019e\3\2\2\2a\u01a1\3\2\2\2c"+
		"\u01a4\3\2\2\2e\u01a7\3\2\2\2g\u01ab\3\2\2\2i\u01af\3\2\2\2k\u01b1\3\2"+
		"\2\2m\u01b4\3\2\2\2o\u01b6\3\2\2\2q\u01b9\3\2\2\2s\u01bc\3\2\2\2u\u01bf"+
		"\3\2\2\2w\u01c4\3\2\2\2y\u01cb\3\2\2\2{\u01cf\3\2\2\2}\u01d3\3\2\2\2\177"+
		"\u01dd\3\2\2\2\u0081\u01df\3\2\2\2\u0083\u01e1\3\2\2\2\u0085\u01e3\3\2"+
		"\2\2\u0087\u01e5\3\2\2\2\u0089\u01e7\3\2\2\2\u008b\u01e9\3\2\2\2\u008d"+
		"\u01eb\3\2\2\2\u008f\u01ed\3\2\2\2\u0091\u01ef\3\2\2\2\u0093\u01f1\3\2"+
		"\2\2\u0095\u01f3\3\2\2\2\u0097\u01f5\3\2\2\2\u0099\u01f7\3\2\2\2\u009b"+
		"\u01f9\3\2\2\2\u009d\u01fb\3\2\2\2\u009f\u01fd\3\2\2\2\u00a1\u01ff\3\2"+
		"\2\2\u00a3\u0201\3\2\2\2\u00a5\u0203\3\2\2\2\u00a7\u0205\3\2\2\2\u00a9"+
		"\u0207\3\2\2\2\u00ab\u0209\3\2\2\2\u00ad\u020b\3\2\2\2\u00af\u020e\3\2"+
		"\2\2\u00b1\u0212\3\2\2\2\u00b3\u0218\3\2\2\2\u00b5\u0226\3\2\2\2\u00b7"+
		"\u00b8\7u\2\2\u00b8\u00b9\7{\2\2\u00b9\u00ba\7u\2\2\u00ba\u00bb\7v\2\2"+
		"\u00bb\u00bc\7g\2\2\u00bc\u00bd\7o\2\2\u00bd\4\3\2\2\2\u00be\u00bf\7r"+
		"\2\2\u00bf\u00c0\7t\2\2\u00c0\u00c1\7q\2\2\u00c1\u00c2\7e\2\2\u00c2\u00c3"+
		"\7g\2\2\u00c3\u00c4\7u\2\2\u00c4\u00c5\7u\2\2\u00c5\6\3\2\2\2\u00c6\u00c7"+
		"\7u\2\2\u00c7\u00c8\7v\2\2\u00c8\u00c9\7c\2\2\u00c9\u00ca\7v\2\2\u00ca"+
		"\u00cb\7g\2\2\u00cb\b\3\2\2\2\u00cc\u00cd\7e\2\2\u00cd\u00ce\7q\2\2\u00ce"+
		"\u00cf\7o\2\2\u00cf\u00d0\7o\2\2\u00d0\u00d1\7k\2\2\u00d1\u00d2\7v\2\2"+
		"\u00d2\n\3\2\2\2\u00d3\u00d4\7w\2\2\u00d4\u00d5\7t\2\2\u00d5\u00d6\7i"+
		"\2\2\u00d6\u00d7\7g\2\2\u00d7\u00d8\7p\2\2\u00d8\u00d9\7v\2\2\u00d9\f"+
		"\3\2\2\2\u00da\u00db\7k\2\2\u00db\u00dc\7p\2\2\u00dc\u00dd\7k\2\2\u00dd"+
		"\u00de\7v\2\2\u00de\16\3\2\2\2\u00df\u00e0\7v\2\2\u00e0\u00e1\7t\2\2\u00e1"+
		"\u00e2\7c\2\2\u00e2\u00e3\7p\2\2\u00e3\u00e4\7u\2\2\u00e4\20\3\2\2\2\u00e5"+
		"\u00e6\7u\2\2\u00e6\u00e7\7g\2\2\u00e7\u00e8\7n\2\2\u00e8\u00e9\7g\2\2"+
		"\u00e9\u00ea\7e\2\2\u00ea\u00eb\7v\2\2\u00eb\22\3\2\2\2\u00ec\u00ed\7"+
		"i\2\2\u00ed\u00ee\7w\2\2\u00ee\u00ef\7c\2\2\u00ef\u00f0\7t\2\2\u00f0\u00f1"+
		"\7f\2\2\u00f1\24\3\2\2\2\u00f2\u00f3\7u\2\2\u00f3\u00f4\7{\2\2\u00f4\u00f5"+
		"\7p\2\2\u00f5\u00f6\7e\2\2\u00f6\26\3\2\2\2\u00f7\u00f8\7c\2\2\u00f8\u00f9"+
		"\7u\2\2\u00f9\u00fa\7u\2\2\u00fa\u00fb\7k\2\2\u00fb\u00fc\7i\2\2\u00fc"+
		"\u00fd\7p\2\2\u00fd\30\3\2\2\2\u00fe\u00ff\7v\2\2\u00ff\u0100\7{\2\2\u0100"+
		"\u0101\7r\2\2\u0101\u0102\7g\2\2\u0102\u0103\7f\2\2\u0103\u0104\7g\2\2"+
		"\u0104\u0105\7h\2\2\u0105\32\3\2\2\2\u0106\u0107\7x\2\2\u0107\u0108\7"+
		"q\2\2\u0108\u0109\7k\2\2\u0109\u010a\7f\2\2\u010a\34\3\2\2\2\u010b\u010c"+
		"\7k\2\2\u010c\u010d\7p\2\2\u010d\u010e\7v\2\2\u010e\36\3\2\2\2\u010f\u0110"+
		"\7e\2\2\u0110\u0111\7n\2\2\u0111\u0112\7q\2\2\u0112\u0113\7e\2\2\u0113"+
		"\u0114\7m\2\2\u0114 \3\2\2\2\u0115\u0116\7e\2\2\u0116\u0117\7j\2\2\u0117"+
		"\u0118\7c\2\2\u0118\u0119\7p\2\2\u0119\"\3\2\2\2\u011a\u011b\7d\2\2\u011b"+
		"\u011c\7q\2\2\u011c\u011d\7q\2\2\u011d\u011e\7n\2\2\u011e$\3\2\2\2\u011f"+
		"\u0120\7u\2\2\u0120\u0121\7e\2\2\u0121\u0122\7c\2\2\u0122\u0123\7n\2\2"+
		"\u0123\u0124\7c\2\2\u0124\u0125\7t\2\2\u0125&\3\2\2\2\u0126\u0127\7u\2"+
		"\2\u0127\u0128\7v\2\2\u0128\u0129\7t\2\2\u0129\u012a\7w\2\2\u012a\u012b"+
		"\7e\2\2\u012b\u012c\7v\2\2\u012c(\3\2\2\2\u012d\u012e\7d\2\2\u012e\u012f"+
		"\7t\2\2\u012f\u0130\7q\2\2\u0130\u0131\7c\2\2\u0131\u0132\7f\2\2\u0132"+
		"\u0133\7e\2\2\u0133\u0134\7c\2\2\u0134\u0135\7u\2\2\u0135\u0136\7v\2\2"+
		"\u0136*\3\2\2\2\u0137\u0138\7e\2\2\u0138\u0139\7q\2\2\u0139\u013a\7p\2"+
		"\2\u013a\u013b\7u\2\2\u013b\u013c\7v\2\2\u013c,\3\2\2\2\u013d\u013e\7"+
		"h\2\2\u013e\u013f\7q\2\2\u013f\u0140\7t\2\2\u0140.\3\2\2\2\u0141\u0142"+
		"\7y\2\2\u0142\u0143\7j\2\2\u0143\u0144\7k\2\2\u0144\u0145\7n\2\2\u0145"+
		"\u0146\7g\2\2\u0146\60\3\2\2\2\u0147\u0148\7f\2\2\u0148\u0149\7q\2\2\u0149"+
		"\62\3\2\2\2\u014a\u014b\7k\2\2\u014b\u014c\7h\2\2\u014c\64\3\2\2\2\u014d"+
		"\u014e\7g\2\2\u014e\u014f\7n\2\2\u014f\u0150\7u\2\2\u0150\u0151\7g\2\2"+
		"\u0151\66\3\2\2\2\u0152\u0153\7t\2\2\u0153\u0154\7g\2\2\u0154\u0155\7"+
		"v\2\2\u0155\u0156\7w\2\2\u0156\u0157\7t\2\2\u0157\u0158\7p\2\2\u01588"+
		"\3\2\2\2\u0159\u015a\7h\2\2\u015a\u015b\7q\2\2\u015b\u015c\7t\2\2\u015c"+
		"\u015d\7c\2\2\u015d\u015e\7n\2\2\u015e\u015f\7n\2\2\u015f:\3\2\2\2\u0160"+
		"\u0161\7g\2\2\u0161\u0162\7z\2\2\u0162\u0163\7k\2\2\u0163\u0164\7u\2\2"+
		"\u0164\u0165\7v\2\2\u0165\u0166\7u\2\2\u0166<\3\2\2\2\u0167\u0168\7q\2"+
		"\2\u0168\u0169\7t\2\2\u0169>\3\2\2\2\u016a\u016b\7k\2\2\u016b\u016c\7"+
		"o\2\2\u016c\u016d\7r\2\2\u016d\u016e\7n\2\2\u016e\u016f\7{\2\2\u016f@"+
		"\3\2\2\2\u0170\u0171\7c\2\2\u0171\u0172\7p\2\2\u0172\u0173\7f\2\2\u0173"+
		"B\3\2\2\2\u0174\u0175\7p\2\2\u0175\u0176\7q\2\2\u0176\u0177\7v\2\2\u0177"+
		"D\3\2\2\2\u0178\u0179\7~\2\2\u0179\u017a\7~\2\2\u017aF\3\2\2\2\u017b\u017c"+
		"\7(\2\2\u017c\u017d\7(\2\2\u017dH\3\2\2\2\u017e\u017f\7>\2\2\u017f\u0180"+
		"\7>\2\2\u0180J\3\2\2\2\u0181\u0182\7@\2\2\u0182\u0183\7@\2\2\u0183L\3"+
		"\2\2\2\u0184\u0185\7?\2\2\u0185\u0186\7?\2\2\u0186N\3\2\2\2\u0187\u0188"+
		"\7#\2\2\u0188\u0189\7?\2\2\u0189P\3\2\2\2\u018a\u018b\7?\2\2\u018bR\3"+
		"\2\2\2\u018c\u018d\7<\2\2\u018d\u018e\7?\2\2\u018eT\3\2\2\2\u018f\u0190"+
		"\7-\2\2\u0190\u0191\7?\2\2\u0191V\3\2\2\2\u0192\u0193\7/\2\2\u0193\u0194"+
		"\7?\2\2\u0194X\3\2\2\2\u0195\u0196\7,\2\2\u0196\u0197\7?\2\2\u0197Z\3"+
		"\2\2\2\u0198\u0199\7\61\2\2\u0199\u019a\7?\2\2\u019a\\\3\2\2\2\u019b\u019c"+
		"\7\'\2\2\u019c\u019d\7?\2\2\u019d^\3\2\2\2\u019e\u019f\7~\2\2\u019f\u01a0"+
		"\7?\2\2\u01a0`\3\2\2\2\u01a1\u01a2\7(\2\2\u01a2\u01a3\7?\2\2\u01a3b\3"+
		"\2\2\2\u01a4\u01a5\7`\2\2\u01a5\u01a6\7?\2\2\u01a6d\3\2\2\2\u01a7\u01a8"+
		"\7>\2\2\u01a8\u01a9\7>\2\2\u01a9\u01aa\7?\2\2\u01aaf\3\2\2\2\u01ab\u01ac"+
		"\7@\2\2\u01ac\u01ad\7@\2\2\u01ad\u01ae\7?\2\2\u01aeh\3\2\2\2\u01af\u01b0"+
		"\7>\2\2\u01b0j\3\2\2\2\u01b1\u01b2\7>\2\2\u01b2\u01b3\7?\2\2\u01b3l\3"+
		"\2\2\2\u01b4\u01b5\7@\2\2\u01b5n\3\2\2\2\u01b6\u01b7\7@\2\2\u01b7\u01b8"+
		"\7?\2\2\u01b8p\3\2\2\2\u01b9\u01ba\7-\2\2\u01ba\u01bb\7-\2\2\u01bbr\3"+
		"\2\2\2\u01bc\u01bd\7/\2\2\u01bd\u01be\7/\2\2\u01bet\3\2\2\2\u01bf\u01c0"+
		"\7v\2\2\u01c0\u01c1\7t\2\2\u01c1\u01c2\7w\2\2\u01c2\u01c3\7g\2\2\u01c3"+
		"v\3\2\2\2\u01c4\u01c5\7h\2\2\u01c5\u01c6\7c\2\2\u01c6\u01c7\7n\2\2\u01c7"+
		"\u01c8\7u\2\2\u01c8\u01c9\7g\2\2\u01c9x\3\2\2\2\u01ca\u01cc\5\u0081A\2"+
		"\u01cb\u01ca\3\2\2\2\u01cc\u01cd\3\2\2\2\u01cd\u01cb\3\2\2\2\u01cd\u01ce"+
		"\3\2\2\2\u01cez\3\2\2\2\u01cf\u01d0\7\60\2\2\u01d0|\3\2\2\2\u01d1\u01d4"+
		"\5\u0083B\2\u01d2\u01d4\5\177@\2\u01d3\u01d1\3\2\2\2\u01d3\u01d2\3\2\2"+
		"\2\u01d4\u01da\3\2\2\2\u01d5\u01d9\5\u0083B\2\u01d6\u01d9\5\177@\2\u01d7"+
		"\u01d9\5\u0081A\2\u01d8\u01d5\3\2\2\2\u01d8\u01d6\3\2\2\2\u01d8\u01d7"+
		"\3\2\2\2\u01d9\u01dc\3\2\2\2\u01da\u01d8\3\2\2\2\u01da\u01db\3\2\2\2\u01db"+
		"~\3\2\2\2\u01dc\u01da\3\2\2\2\u01dd\u01de\7a\2\2\u01de\u0080\3\2\2\2\u01df"+
		"\u01e0\t\2\2\2\u01e0\u0082\3\2\2\2\u01e1\u01e2\t\3\2\2\u01e2\u0084\3\2"+
		"\2\2\u01e3\u01e4\7*\2\2\u01e4\u0086\3\2\2\2\u01e5\u01e6\7+\2\2\u01e6\u0088"+
		"\3\2\2\2\u01e7\u01e8\7]\2\2\u01e8\u008a\3\2\2\2\u01e9\u01ea\7_\2\2\u01ea"+
		"\u008c\3\2\2\2\u01eb\u01ec\7}\2\2\u01ec\u008e\3\2\2\2\u01ed\u01ee\7\177"+
		"\2\2\u01ee\u0090\3\2\2\2\u01ef\u01f0\7.\2\2\u01f0\u0092\3\2\2\2\u01f1"+
		"\u01f2\7<\2\2\u01f2\u0094\3\2\2\2\u01f3\u01f4\7=\2\2\u01f4\u0096\3\2\2"+
		"\2\u01f5\u01f6\7(\2\2\u01f6\u0098\3\2\2\2\u01f7\u01f8\7`\2\2\u01f8\u009a"+
		"\3\2\2\2\u01f9\u01fa\7~\2\2\u01fa\u009c\3\2\2\2\u01fb\u01fc\7#\2\2\u01fc"+
		"\u009e\3\2\2\2\u01fd\u01fe\7A\2\2\u01fe\u00a0\3\2\2\2\u01ff\u0200\7\'"+
		"\2\2\u0200\u00a2\3\2\2\2\u0201\u0202\7-\2\2\u0202\u00a4\3\2\2\2\u0203"+
		"\u0204\7/\2\2\u0204\u00a6\3\2\2\2\u0205\u0206\7,\2\2\u0206\u00a8\3\2\2"+
		"\2\u0207\u0208\7\61\2\2\u0208\u00aa\3\2\2\2\u0209\u020a\7\u0080\2\2\u020a"+
		"\u00ac\3\2\2\2\u020b\u020c\7>\2\2\u020c\u020d\7/\2\2\u020d\u00ae\3\2\2"+
		"\2\u020e\u020f\7/\2\2\u020f\u0210\7@\2\2\u0210\u00b0\3\2\2\2\u0211\u0213"+
		"\t\4\2\2\u0212\u0211\3\2\2\2\u0213\u0214\3\2\2\2\u0214\u0212\3\2\2\2\u0214"+
		"\u0215\3\2\2\2\u0215\u0216\3\2\2\2\u0216\u0217\bY\2\2\u0217\u00b2\3\2"+
		"\2\2\u0218\u0219\7\61\2\2\u0219\u021a\7,\2\2\u021a\u021e\3\2\2\2\u021b"+
		"\u021d\13\2\2\2\u021c\u021b\3\2\2\2\u021d\u0220\3\2\2\2\u021e\u021f\3"+
		"\2\2\2\u021e\u021c\3\2\2\2\u021f\u0221\3\2\2\2\u0220\u021e\3\2\2\2\u0221"+
		"\u0222\7,\2\2\u0222\u0223\7\61\2\2\u0223\u0224\3\2\2\2\u0224\u0225\bZ"+
		"\2\2\u0225\u00b4\3\2\2\2\u0226\u0227\7\61\2\2\u0227\u0228\7\61\2\2\u0228"+
		"\u022c\3\2\2\2\u0229\u022b\n\5\2\2\u022a\u0229\3\2\2\2\u022b\u022e\3\2"+
		"\2\2\u022c\u022a\3\2\2\2\u022c\u022d\3\2\2\2\u022d\u022f\3\2\2\2\u022e"+
		"\u022c\3\2\2\2\u022f\u0230\b[\2\2\u0230\u00b6\3\2\2\2\n\2\u01cd\u01d3"+
		"\u01d8\u01da\u0214\u021e\u022c\3\b\2\2";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}