(function() {var implementors = {
"async_io":[["impl&lt;T: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/std/os/fd/owned/trait.AsFd.html\" title=\"trait std::os::fd::owned::AsFd\">AsFd</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/std/os/fd/owned/trait.AsFd.html\" title=\"trait std::os::fd::owned::AsFd\">AsFd</a> for <a class=\"struct\" href=\"async_io/struct.Async.html\" title=\"struct async_io::Async\">Async</a>&lt;T&gt;"]],
"async_process":[["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/std/os/fd/owned/trait.AsFd.html\" title=\"trait std::os::fd::owned::AsFd\">AsFd</a> for <a class=\"struct\" href=\"async_process/struct.ChildStdin.html\" title=\"struct async_process::ChildStdin\">ChildStdin</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/std/os/fd/owned/trait.AsFd.html\" title=\"trait std::os::fd::owned::AsFd\">AsFd</a> for <a class=\"struct\" href=\"async_process/struct.ChildStderr.html\" title=\"struct async_process::ChildStderr\">ChildStderr</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/std/os/fd/owned/trait.AsFd.html\" title=\"trait std::os::fd::owned::AsFd\">AsFd</a> for <a class=\"struct\" href=\"async_process/struct.ChildStdout.html\" title=\"struct async_process::ChildStdout\">ChildStdout</a>"]],
"io_lifetimes":[],
"polling":[["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/std/os/fd/owned/trait.AsFd.html\" title=\"trait std::os::fd::owned::AsFd\">AsFd</a> for <a class=\"struct\" href=\"polling/struct.Poller.html\" title=\"struct polling::Poller\">Poller</a>"]],
"rustix":[["impl&lt;'fd&gt; <a class=\"trait\" href=\"rustix/fd/trait.AsFd.html\" title=\"trait rustix::fd::AsFd\">AsFd</a> for <a class=\"struct\" href=\"rustix/io/struct.PollFd.html\" title=\"struct rustix::io::PollFd\">PollFd</a>&lt;'fd&gt;"]],
"tokio":[["impl&lt;T: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/std/os/fd/raw/trait.AsRawFd.html\" title=\"trait std::os::fd::raw::AsRawFd\">AsRawFd</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/std/os/fd/owned/trait.AsFd.html\" title=\"trait std::os::fd::owned::AsFd\">AsFd</a> for <a class=\"struct\" href=\"tokio/io/unix/struct.AsyncFd.html\" title=\"struct tokio::io::unix::AsyncFd\">AsyncFd</a>&lt;T&gt;"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/std/os/fd/owned/trait.AsFd.html\" title=\"trait std::os::fd::owned::AsFd\">AsFd</a> for <a class=\"struct\" href=\"tokio/net/struct.TcpStream.html\" title=\"struct tokio::net::TcpStream\">TcpStream</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/std/os/fd/owned/trait.AsFd.html\" title=\"trait std::os::fd::owned::AsFd\">AsFd</a> for <a class=\"struct\" href=\"tokio/net/struct.UdpSocket.html\" title=\"struct tokio::net::UdpSocket\">UdpSocket</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/std/os/fd/owned/trait.AsFd.html\" title=\"trait std::os::fd::owned::AsFd\">AsFd</a> for <a class=\"struct\" href=\"tokio/net/struct.UnixListener.html\" title=\"struct tokio::net::UnixListener\">UnixListener</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/std/os/fd/owned/trait.AsFd.html\" title=\"trait std::os::fd::owned::AsFd\">AsFd</a> for <a class=\"struct\" href=\"tokio/net/struct.TcpListener.html\" title=\"struct tokio::net::TcpListener\">TcpListener</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/std/os/fd/owned/trait.AsFd.html\" title=\"trait std::os::fd::owned::AsFd\">AsFd</a> for <a class=\"struct\" href=\"tokio/net/struct.UnixDatagram.html\" title=\"struct tokio::net::UnixDatagram\">UnixDatagram</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/std/os/fd/owned/trait.AsFd.html\" title=\"trait std::os::fd::owned::AsFd\">AsFd</a> for <a class=\"struct\" href=\"tokio/process/struct.ChildStdout.html\" title=\"struct tokio::process::ChildStdout\">ChildStdout</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/std/os/fd/owned/trait.AsFd.html\" title=\"trait std::os::fd::owned::AsFd\">AsFd</a> for <a class=\"struct\" href=\"tokio/net/unix/pipe/struct.Sender.html\" title=\"struct tokio::net::unix::pipe::Sender\">Sender</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/std/os/fd/owned/trait.AsFd.html\" title=\"trait std::os::fd::owned::AsFd\">AsFd</a> for <a class=\"struct\" href=\"tokio/net/unix/pipe/struct.Receiver.html\" title=\"struct tokio::net::unix::pipe::Receiver\">Receiver</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/std/os/fd/owned/trait.AsFd.html\" title=\"trait std::os::fd::owned::AsFd\">AsFd</a> for <a class=\"struct\" href=\"tokio/fs/struct.File.html\" title=\"struct tokio::fs::File\">File</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/std/os/fd/owned/trait.AsFd.html\" title=\"trait std::os::fd::owned::AsFd\">AsFd</a> for <a class=\"struct\" href=\"tokio/process/struct.ChildStdin.html\" title=\"struct tokio::process::ChildStdin\">ChildStdin</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/std/os/fd/owned/trait.AsFd.html\" title=\"trait std::os::fd::owned::AsFd\">AsFd</a> for <a class=\"struct\" href=\"tokio/net/struct.TcpSocket.html\" title=\"struct tokio::net::TcpSocket\">TcpSocket</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/std/os/fd/owned/trait.AsFd.html\" title=\"trait std::os::fd::owned::AsFd\">AsFd</a> for <a class=\"struct\" href=\"tokio/net/struct.UnixStream.html\" title=\"struct tokio::net::UnixStream\">UnixStream</a>"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/std/os/fd/owned/trait.AsFd.html\" title=\"trait std::os::fd::owned::AsFd\">AsFd</a> for <a class=\"struct\" href=\"tokio/process/struct.ChildStderr.html\" title=\"struct tokio::process::ChildStderr\">ChildStderr</a>"]]
};if (window.register_implementors) {window.register_implementors(implementors);} else {window.pending_implementors = implementors;}})()