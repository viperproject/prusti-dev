/// Source: https://docs.rs/same-file/1.0.4/src/same_file/lib.rs.html#326-328
extern crate prusti_contracts;

pub type c_int = i32;

pub struct FileDesc {
    fd: c_int,
}

pub struct SysFsFile(FileDesc);

pub struct StdFsFile {
    inner: SysFsFile,
}

pub struct UnixImplHandle {
    file: Option<StdFsFile>,
    // If is_std is true, then we don't drop the corresponding File since it
    // will close the handle.
    is_std: bool,
    dev: u64,
    ino: u64,
}

impl UnixImplHandle {
    #[trusted]
    pub fn as_file_mut(&mut self) -> &mut StdFsFile {
        // unwrap() will not panic. Since we were able to open the
        // file successfully, then `file` is guaranteed to be Some()
        self.file.as_mut().take().unwrap()
    }
}

pub struct Handle(UnixImplHandle);

impl Handle {
    pub fn as_file_mut(&mut self) -> &mut StdFsFile {
        self.0.as_file_mut()
    }
}

fn main() {}
