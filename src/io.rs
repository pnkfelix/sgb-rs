use super::Long;

use std::io::BufferedReader;
use std::io::File;
use std::num::ToPrimitive;

/// The external variable io errors mentioned in the previous section
/// will be set nonzero if any anomalies are detected. Errors won’t
/// occur in normal use of GraphBase programs, so no attempt has been
/// made to provide a user-friendly way to decode the nonzero values
/// that io errors might assume. Information is simply gathered in
/// binary form; system wizards who might need to do a bit of
/// troubleshooting should be able to decode io errors without great
/// pain
#[derive(Copy, Debug)]
pub enum Error {
    /// bit set in io errors if fopen fails
    CantOpenFile         = 0x1,
    /// /∗ bit set if fclose fails ∗/
    CantCloseFile        = 0x2,
    /// bit set if the data file’s first line isn’t legit
    BadFirstLine         = 0x4,
    /// bit set if the second line doesn’t pass muster
    BadSecondLine        = 0x8,
    /// bit set if the third line is awry
    BadThirdLine         = 0x10,
    /// guess when this bit is set
    BadFourthLine        = 0x20,
    /// bit set if fgets fails
    FileEndedPrematurely = 0x40,
    /// bit set if line is too long or ’\n’ is missing
    MissingNewline       = 0x80,
    /// bit set if the line count is wrong
    WrongNumberOfLines   = 0x100,
    /// bit set if the checksum is wrong
    WrongChecksum        = 0x200,
    /// bit set if user tries to close an unopened file
    NoFileOpen           = 0x400,
    /// bit set if final line has incorrect form
    BadLastLine          = 0x800,
}

#[test]
fn main_test() {
    // <test the gb_open routine>
    let mut c = Context::open(Path::new("test.dat"))
        .unwrap_or_else(|:e| panic!("open test.dat failed, {:?}", e));

    // <test the sample data lines>
    test_the_sample_data_lines(&mut c);

    // <test the gb_close routine>
    c.close().unwrap_or_else(|:e| panic!("close failed, {:?}", e));
}

pub struct Context {
    io_errors: Long,
    filename: String,
    cur_file: BufferedReader<File>,
    cur_line: String,
    cur_line_offset: i8,

    /// mapping of characters to internal codes
    icode: [i8; 256],
    /// current checksum value
    magic: Long,
    /// current line number in file
    line_no: Long,
    /// desired final magic number
    final_magic: Long,
    /// total number of data lines
    tot_lines: Long,
    /// is there data still waiting to be read?
    more_data: bool,
}

impl Context {
    fn raw_open(filename: String, f: File) -> Context {
        let mut c = Context {
            io_errors: 0,
            filename: filename,
            cur_file: BufferedReader::new(f),
            cur_line: String::new(),
            cur_line_offset: 0,
            icode: Context::icode_setup(),
            magic: 0,
            line_no: 0,
            final_magic: 0,
            // allow "infinitely many" lines
            tot_lines: 0x7fffffff,
            more_data: true,
        };
        c.fill_buf();
        c
    }

    fn cur_pos(&self) -> char {
        debug!("cur_pos line.len: {} cur_line_offset: {}",
               self.cur_line.len(), self.cur_line_offset);
        if self.cur_line_offset.to_uint().unwrap() == self.cur_line.len() {
            '\0'
        } else {
            self.cur_line.char_at(self.cur_line_offset as usize)
        }
    }

    fn incr_cur_pos(&mut self) {
        self.cur_line_offset += 1;
    }
}

impl Context {
    pub fn fill_buf(&mut self) {
        match self.cur_file.read_line() {
            Ok(s) => {
                println!("fill_buf read: {}", s);
                self.cur_line = s;
                self.cur_line_offset = 0;
            }
            Err(_) => {
                self.io_errors |= Error::FileEndedPrematurely as Long;
                self.cur_line = String::new();
                self.more_data = false;
                return;
            }
        }
        let saw_newline;
        let blanks = {
            let mut chars = self.cur_line.chars().rev();
            saw_newline = if let Some('\n') = chars.next() {
                // okay
                true
            } else {
                self.io_errors |= Error::MissingNewline as Long;
                chars = self.cur_line.chars().rev();
                false
            };
            // count trailing blanks
            let blanks = chars.take_while(|c| *c == ' ').count();
            blanks
        };
        if blanks > 0 {
            let s : String = self.cur_line.chars().take(self.cur_line.chars().count() - blanks - if saw_newline { 1 } else { 0 }).collect();
            self.cur_line = s + "\n";
        }
    }
}

/// large prime such that 2p + unexpected_char won't overflow
const CHECKSUM_PRIME: Long = (1 << 30) - 83;

/// The icode mapping is defined by a single string, imap, such that
/// character imap[k] has icode value k. There are 96 characters in
/// imap, namely the 94 standard visible ASCII codes plus space and
/// newline. If EBCDIC code is used instead of ASCII, the cents sign
/// c/ should take the place of single-left-quote ‘, and ¬ should take
/// the place of ~.
///
/// All characters that don’t appear in imap are given the same icode
/// value, called unexpected char. Such characters should be avoided
/// in GraphBase files whenever possible. (If they do appear, they can
/// still get into a user’s data, but we don’t distinguish them from
/// each other for checksumming purposes.)
///
/// The icode table actually plays a dual role, because we’ve rigged
/// it so that codes 0–15 come from the characters
/// "0123456789ABCDEF". This facilitates conversion of decimal and
/// hexadecimal data. We can also use it for radices higher than 16.
const IMAP: &'static str =
    "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ\
     abcdefghijklmnopqrstuvwxyz_^~&@,;.:?!%#$+-*/|\\<=>()[]{}`'\" \n";
const UNEXPECTED_CHAR: i8 = 127;

pub fn imap_chr(d: Long) -> char {
    if d < 0 || d as usize >= IMAP.len() {
        '\0'
    } else {
        IMAP.char_at(d as usize)
    }
}

impl Context {
    pub fn imap_ord(&self, c: i8) -> Long {
        let c = c as Long;
        self.make_sure_that_icode_has_been_initialized();
        (if c < 0 || c > 255 {
            debug!("imap_ord c: {} unexpected_char", c);
            UNEXPECTED_CHAR
        } else {
            let ret = self.icode[c as usize];
            debug!("imap_ord c: {} ret: {}", c, ret);
            ret
        }) as Long
    }

    fn make_sure_that_icode_has_been_initialized(&self) {
        assert!(0 != self.icode['1' as usize]);
    }

    fn icode_setup() -> [i8; 256] {
        let mut icode = [UNEXPECTED_CHAR; 256];
        for (k, p) in IMAP.bytes().enumerate() {
            println!("init icode[{}] = {}", p, k);
            icode[p as usize] = k.to_i8().unwrap();
        }
        icode
    }
}

impl Context {
    /// advance to the next line of the data file
    pub fn newline(&mut self) {
        self.line_no += 1;
        if self.line_no > self.tot_lines {
            self.more_data = false;
        }
        if self.more_data {
            self.fill_buf();
            if self.cur_line.char_at(0) != '*' {
                let new_magic = self.new_checksum(self.cur_line.as_slice(),
                                                  self.magic);
                println!("magic old: {} new: {}", self.magic, new_magic);
                self.magic = new_magic;
            }
        }
    }

    /// compute change in magic number
    fn new_checksum(&self, s: &str, old_checksum: Long) -> Long {
        let mut a = old_checksum;
        for p in s.bytes() {
            let p2 = p.to_i8().unwrap();
            let imap_ord = self.imap_ord(p2);
            println!("checksum interm a: {} p: {} {} imap_ord: {}", a, p as char, p2, imap_ord);
                     
            a = (a + a + imap_ord) % CHECKSUM_PRIME;
        }
        a
    }

    /// has the data all been read?
    pub fn eof(&self) -> bool {
        !self.more_data
    }
}

/// The user can input characters from the buffer in several
/// ways. First, there’s a basic gb char ( ) routine, which
/// returns a single character. The character is ’\n’ if the last
/// character on the line has already been read (and it continues
/// to be ’\n’ until the user calls gb newline).
///
/// The current position in the line, cur pos, always advances
/// when gb char is called, unless cur pos was already at the end
/// of the line. There’s also a gb backup ( ) routine, which moves
/// cur pos one place to the left unless it was already at the
/// beginning.
impl Context {
    /// get next character of current line, or '\n'
    pub fn char(&mut self) -> char {
        if self.cur_line_offset < self.cur_line.len().to_i8().unwrap() {
            let c = self.cur_line.char_at(self.cur_line_offset.to_uint().unwrap());
            self.cur_line_offset += 1;
            return c;
        } else {
            return '\n';
        }
    }

    /// move back ready to scan a character again
    pub fn backup(&mut self) {
        if self.cur_line_offset > 0 {
            self.cur_line_offset -= 1;
        }
    }
}

/// There are two ways to read numerical data. The first, gb digit(d),
/// expects to read a single character in radix d, using icode values
/// to specify digits greater than 9. (Thus, for example, ’A’
/// represents the hexadecimal digit for decimal 10.) If the next
/// character is a valid d-git, cur pos moves to the next character
/// and the numerical value is returned. Otherwise cur pos stays in
/// the same place and −1 is returned.
///
/// The second routine, gb number (d), reads characters and forms an
/// unsigned radix-d number until the first non-digit is
/// encountered. The resulting number is returned; it is zero if no
/// digits were found. No errors are possible with this routine,
/// because it uses unsigned long arithmetic.
impl Context {
    /// The value of d should be at most 127; in most applications, d
    /// is of course either 10 or 16.
    pub fn digit(&mut self, d: i8) -> Long {
        self.icode[0] = d; // make sure ’\0’ is a nondigit
        let cur_pos = (self.cur_pos() as u32).to_i8().unwrap();
        if self.imap_ord(cur_pos) < d.to_i32().unwrap() {
            let l = self.icode[cur_pos.to_uint().unwrap()];
            self.incr_cur_pos();
            return l.to_i32().unwrap();
        } else {
            return -1;
        }
    }

    pub fn number(&mut self, d: i8) -> Long {
        let mut a: Long = 0;
        self.icode[0] = d; // make sure ’\0’ is a nondigit
        let d = d as Long;
        debug!("imap: {}", IMAP);
        debug!("icode: {:?}", self.icode.as_slice());
        loop {
            let c = self.cur_pos();
            let cur_pos = (c as u32).to_i8().unwrap();
            let o = self.imap_ord(cur_pos);
            println!("number loop c: {:?} cur_pos: {} o: {} d: {}", c, cur_pos, o, d);
            if o < d {
                a = a * d + self.icode[cur_pos as usize] as Long;
                self.incr_cur_pos();
            } else {
                break;
            }
        }
        return a;
    }
}

impl Context {
    pub fn string(&mut self, c: char) -> String {
        let mut s = String::new();
        for curr in self.cur_line
            .slice_from(self.cur_line_offset as usize)
            .chars() {
            if curr == c {
                break;
            }
            s.push(curr);
        }
        s
    }
}

#[cfg(test)]
fn test_the_sample_data_lines(c: &mut Context) {
    if c.number(10) != 123456789 {
        // decimal number not working
        c.io_errors |= 1 << 20;
    }
    if c.digit(16) != 10 {
        // we missed the A following the decimal number
        c.io_errors |= 1 << 21;
    }
    // get set to read ‘9A’ again
    c.backup(); c.backup();

    if c.number(16) != 0x9ABCDEF {
        // hexadecimal number not working
        c.io_errors |= 1 << 22;
    }
    // now we should be scanning a blank line
    c.newline();
    if c.char() != '\n' {
        // newline not inserted at end
        c.io_errors |= 1 << 23;
    }
    if c.char() != '\n' {
        // newline not implied after end
        c.io_errors |= 1 << 24;
    }
    if c.number(60) != 0 {
        // number should stop at null character
        c.io_errors |= 1 << 25;
    }
    let s = c.string('\n');
    if s != "" {
        // string should be null after end of line
        println!("c.string('\\n'): {:?}", s);
        c.io_errors |= 1 << 26;
    }
    c.newline();
    let s = c.string(':');
    if s != "Oops" {
        // string not read properly
        println!("c.string(':'): {:?}", s);
        c.io_errors |= 1 << 27;
    }
    if c.io_errors != 0 {
        panic!("Sorry it failed, error code: {:b}", c.io_errors);
    }
    if c.digit(10) != -1 {
        panic!("Digit error not detected");
    }
    if c.char() != ':' {
        // lost synch after .string and .digit
        c.io_errors |= 1 << 28;
    }
    if c.eof() {
        // premature end-of-file indication
        c.io_errors |= 1 << 29;
    }
    c.newline();
    if !c.eof() {
        c.io_errors |= 1 << 30;
    }
}

impl Context {
    pub fn open(path: Path) -> Result<Context, Error> {
        File::open(&path)
            .map_err(|_| Error::CantOpenFile)
            .and_then(|f| {
                let filename = format!("{}", path.filename_display());
                let mut c = Context::raw_open(filename, f);
                try!(c.check_first_line());
                try!(c.check_second_line());
                try!(c.check_third_line());
                try!(c.check_fourth_line());
                c.newline(); // the first line of real data is now in the buffer
                Ok(c)
            })
    }
}

/// The first four lines of a typical data file should look something like this:
///
/// ```text
///  * File "words.dat" from the Stanford GraphBase (C) 1993 Stanford University\cr
///  * A database of English five-letter words\cr
///  * This file may be freely copied but please do not change it in any way!\cr
///  * (Checksum parameters 5757,526296596)\cr}$$
/// ```
///
/// We actually verify only that the first four lines of a data file named |"foo"|
/// begin respectively with the characters
///
/// ```text
///  * File "foo"
///  *
///  *
///  * (Checksum parameters $l$,$m$)
/// ```
///
/// where `$l$` and `$m$` are decimal numbers. The values of `$l$` and
/// `$m$` are stored away as |tot_lines| and |final_magic|, to be
/// matched at the end of the file.
impl Context {
    fn check_first_line(&mut self) -> Result<(), Error> {
        let expect = format!("* File \"{}\"", self.filename);
        if self.cur_line.slice_to(expect.len()) != expect {
            return Err(Error::BadFirstLine);
        }
        Ok(())
    }

    fn check_second_line(&mut self) -> Result<(), Error> {
        self.fill_buf();
        if self.cur_line.char_at(0) != '*' {
            return Err(Error::BadSecondLine);
        }
        Ok(())
    }

    fn check_third_line(&mut self) -> Result<(), Error> {
        self.fill_buf();
        if self.cur_line.char_at(0) != '*' {
            return Err(Error::BadThirdLine)
        }
        Ok(())
    }

    fn check_fourth_line(&mut self) -> Result<(), Error> {
        self.fill_buf();
        let expect = "* (Checksum parameters ";
        {
            let actual = self.cur_line.slice_to(expect.len());
            if actual != expect {
                println!("whoops 1, actual: {}", actual);
                return Err(Error::BadFourthLine);
            }
        }
        self.cur_line_offset += expect.len().to_i8().unwrap();
        self.tot_lines = self.number(10);
        let c = self.char();
        if c != ',' {
            println!("whoops 2, c: {} tot_lines; {}", c, self.tot_lines);
            return Err(Error::BadFourthLine);
        }
        self.final_magic = self.number(10);
        let c = self.char();
        if c != ")".char_at(0) { // (workaround emacs mode bug)
            println!("whoops 3, c: {} final_magic; {}", c, self.final_magic);
            return Err(Error::BadFourthLine);
        }
        Ok(())
    }
}

/// Closing a file. After all data has been input, or should have been
/// input, we check that the file was open and that it had the correct
/// number of lines, the correct magic number, and a correct final
/// line. The subroutine gb close, like gb open, returns the value of
/// io errors, which will be nonzero if at least one problem was
/// noticed.
impl Context {
    pub fn close(mut self) -> Result<(), Error> {
        self.fill_buf();
        let expect = format!("* End of file \"{}\"",
                             self.filename);
        if self.cur_line.slice_to(expect.len()) != expect {
            return Err(Error::BadLastLine)
        }
        self.more_data = false;
        self.cur_line = String::new();
        self.cur_line_offset = 0;
        if self.line_no != self.tot_lines + 1 {
            return Err(Error::WrongNumberOfLines);
        }
        if self.magic != self.final_magic {
            debug!("magic: {} final_magic: {}", self.magic, self.final_magic);
            return Err(Error::WrongChecksum);
        }
        Ok(())
    }
}

/// There is also a less paranoid routine, gb raw close, that closes
/// user-generated files. It simply closes the current file, if any,
/// and returns the value of the magic checksum.
///
/// Example: The restore graph subroutine in GB SAVE uses gb raw open
/// and gb raw close to provide system- independent input that is
/// almost as foolproof as the reading of standard GraphBase data.
impl Context {
    pub fn raw_close(mut self) -> Long {
        self.more_data = false;
        self.cur_line = String::new();
        self.cur_line_offset = 0;
        return self.magic;
    }
}
