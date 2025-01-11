# Builder image for Nix environment
FROM nixos/nix:latest AS nix-builder

# Enable experimental features for Nix to use flakes
RUN nix-env -iA nixpkgs.nixFlakes \
    && echo "experimental-features = nix-command flakes" >> /etc/nix/nix.conf

RUN nix-shell -p neofetch --run neofetch

# Ubuntu base image for other dependencies
FROM ubuntu:24.04 AS ubuntu-base

# Update apt
RUN apt-get update

# Install nix deps to ubuntu
RUN apt-get install -y \
    curl \
    xz-utils \
    bzip2 \
    git \
    build-essential \
    ssh \
    wget

RUN groupadd -r nixbld \
    && for i in $(seq 1 10); do useradd -r -g nixbld -G nixbld -d /var/empty -s /sbin/nologin -c "Nix build user $i" nixbld$i; done

# Copy nix store from nix-builder
COPY --from=nix-builder /nix /nix
COPY --from=nix-builder /root/.nix-profile /root/.nix-profile
COPY --from=nix-builder /etc/nix/nix.conf /etc/nix/nix.conf

# Ensure Nix binaries are in PATH
ENV PATH=/root/.nix-profile/bin:$PATH
ENV NIX_PATH=/nix/var/nix/profiles/per-user/root/channels
ENV NIX_SSL_CERT_FILE=/etc/ssl/certs/ca-certificates.crt

RUN nix-shell -p neofetch --run neofetch

WORKDIR /home/ubuntu
