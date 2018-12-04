#!/bin/bash

# Create user “developer” with UID equal to the one that owns
# directory “workspace”.
USER_ID=$(stat -c "%u" /home/developer/)
echo "developer:x:${USER_ID}:${USER_ID}:Developer,,,:/home/developer:/bin/bash" >> /etc/passwd
echo "developer:x:${USER_ID}:" >> /etc/group
echo "developer ALL=(ALL) NOPASSWD: ALL" > /etc/sudoers.d/developer
chmod 0440 /etc/sudoers.d/developer
chown root:root /usr/bin/sudo && chmod 4755 /usr/bin/sudo
PASS=$(< /dev/urandom tr -dc _A-Z-a-z-0-9 | head -c${1:-32};echo;)
echo "developer:${PASS}" | chpasswd

# Start SSH server.
/usr/sbin/sshd -D
