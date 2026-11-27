FROM ubuntu:24.04
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends \
      git curl ca-certificates bubblewrap time procps jq python3 xz-utils zstd \
    && rm -rf /var/lib/apt/lists/*
ENV ELAN_HOME=/opt/elan
RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan-init.sh \
    && sh /tmp/elan-init.sh -y --default-toolchain none --no-modify-path \
    && /opt/elan/bin/elan toolchain install leanprover/lean4:v4.37.0-rc1 \
    && /opt/elan/bin/elan default leanprover/lean4:v4.37.0-rc1 \
    && rm /tmp/elan-init.sh && chmod -R a+rX /opt/elan
ENV PATH=/opt/elan/toolchains/leanprover--lean4---v4.37.0-rc1/bin:/opt/elan/bin:$PATH
# lake check/comparator bwrap mounts a tmpfs on /run/user, which ubuntu:24.04 images lack.
RUN mkdir -p /run/user && chmod 755 /run/user
# Unprivileged user: lake check/comparator must not run as a privileged user.
RUN userdel -r ubuntu 2>/dev/null || true; useradd -m -u 1000 -s /bin/bash checker
USER checker
WORKDIR /work
