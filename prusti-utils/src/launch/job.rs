// Copied and modified from cargo/rustup
// https://github.com/rust-lang/rustup/blob/affbdfe0a37d92444e7c3c111043cd336e2f7728/src/cli/job.rs

// Copyright Diggory Blake, the Mozilla Corporation, and Rustup contributors.
//
// Licensed under either of
//
// Apache License, Version 2.0, (LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0)
// MIT license (LICENSE-MIT or https://opensource.org/licenses/MIT)
// at your option.

//! # Job management on Windows:
//!
//! Most of the time when you're running cargo you expect Ctrl-C to actually
//! terminate the entire tree of processes in play, not just the one at the top
//! (cargo). This currently works "by default" on Unix platforms because Ctrl-C
//! actually sends a signal to the *process group* rather than the parent
//! process, so everything will get torn down. On Windows, however, this does
//! not happen and Ctrl-C just kills cargo.
//!
//! To achieve the same semantics on Windows we use Job Objects to ensure that
//! all processes die at the same time. Job objects have a mode of operation
//! where when all handles to the object are closed it causes all child
//! processes associated with the object to be terminated immediately.
//! Conveniently whenever a process in the job object spawns a new process the
//! child will be associated with the job object as well. This means if we add
//! ourselves to the job object we create then everything will get torn down!
//!
//! # Job management on Unix:
//!
//! We register a SIGINT handler that kills the process group.

#![allow(clippy::missing_safety_doc)]

pub use self::imp::Setup;

pub fn setup() -> Option<Setup> {
    unsafe { imp::setup() }
}

#[cfg(unix)]
mod imp {
    use nix::{
        sys::signal::{killpg, Signal},
        unistd::{getpgrp, setpgid, Pid},
    };

    pub type Setup = bool;

    fn sigint_handler() {
        // Killing the process group terminates the process tree
        killpg(getpgrp(), Signal::SIGKILL).expect("Error killing process tree.");
    }

    pub(super) unsafe fn setup() -> Option<Setup> {
        // Move process to group leader if it isn't. The only applicable error should be EPERM which
        // can be thrown when the process is already the group leader. Thus, we ignore it.
        let _ = setpgid(Pid::this(), Pid::this());
        // Register the SIGINT handler
        ctrlc::set_handler(sigint_handler).expect("Error setting Ctrl-C handler");
        Some(false)
    }
}

#[cfg(windows)]
mod imp {
    use std::{io, mem, ptr};

    use winapi::{
        shared::minwindef::*,
        um::{
            handleapi::*,
            jobapi2::*,
            processthreadsapi::*,
            winnt::{HANDLE, *},
        },
    };

    pub struct Setup {
        job: Handle,
    }

    struct Handle {
        inner: HANDLE,
    }

    fn last_err() -> io::Error {
        io::Error::last_os_error()
    }

    pub(super) unsafe fn setup() -> Option<Setup> {
        // Creates a new job object for us to use and then adds ourselves to it.
        // Note that all errors are basically ignored in this function,
        // intentionally. Job objects are "relatively new" in Windows,
        // particularly the ability to support nested job objects. Older
        // Windows installs don't support this ability. We probably don't want
        // to force Cargo to abort in this situation or force others to *not*
        // use job objects, so we instead just ignore errors and assume that
        // we're otherwise part of someone else's job object in this case.

        let job = CreateJobObjectW(ptr::null_mut(), ptr::null());
        if job.is_null() {
            return None;
        }
        let job = Handle { inner: job };

        // Indicate that when all handles to the job object are gone that all
        // process in the object should be killed. Note that this includes our
        // entire process tree by default because we've added ourselves and
        // our children will reside in the job once we spawn a process.
        let mut info: JOBOBJECT_EXTENDED_LIMIT_INFORMATION;
        info = mem::zeroed();
        info.BasicLimitInformation.LimitFlags = JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE;
        let r = SetInformationJobObject(
            job.inner,
            JobObjectExtendedLimitInformation,
            &mut info as *mut _ as LPVOID,
            mem::size_of_val(&info) as DWORD,
        );
        if r == 0 {
            return None;
        }

        // Assign our process to this job object, meaning that our children will
        // now live or die based on our existence.
        let me = GetCurrentProcess();
        let r = AssignProcessToJobObject(job.inner, me);
        if r == 0 {
            return None;
        }

        Some(Setup { job })
    }

    impl Drop for Setup {
        fn drop(&mut self) {
            // On normal exits (not ctrl-c), we don't want to kill any child
            // processes. The destructor here configures our job object to
            // *not* kill everything on close, then closes the job object.
            unsafe {
                let mut info: JOBOBJECT_EXTENDED_LIMIT_INFORMATION;
                info = mem::zeroed();
                let r = SetInformationJobObject(
                    self.job.inner,
                    JobObjectExtendedLimitInformation,
                    &mut info as *mut _ as LPVOID,
                    mem::size_of_val(&info) as DWORD,
                );
                if r == 0 {
                    log::info!("failed to configure job object to defaults: {}", last_err());
                }
            }
        }
    }

    impl Drop for Handle {
        fn drop(&mut self) {
            unsafe {
                CloseHandle(self.inner);
            }
        }
    }
}
